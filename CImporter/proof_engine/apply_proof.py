"""Apply a tactic proof to a sorry location, check with lake build, retry on failure.

The apply-check-retry loop:
1. Parse the LLM response to extract the tactic block
2. Replace sorry in the .lean file with the tactic
3. Run `lake build <module>` to kernel-check
4. If success: done
5. If error: capture error, build retry prompt, iterate (up to max_retries)

Trust model: the LLM is UNTRUSTED. Only proofs accepted by Lean's kernel
(via successful `lake build`) are considered valid.
"""

import re
import shutil
import subprocess
import logging
from dataclasses import dataclass
from pathlib import Path
from typing import Optional

from .extract_goals import SorryGoal

logger = logging.getLogger(__name__)


@dataclass
class ProofResult:
    """Result of attempting to apply a proof."""
    goal: SorryGoal
    success: bool
    tactic: str
    # Error message if failed
    error: Optional[str] = None
    # Number of attempts made
    attempts: int = 0


def extract_tactic_from_response(response: str) -> str:
    """Extract the tactic block from an LLM response.

    Handles:
    - Markdown fenced code blocks (```lean ... ```)
    - Plain text tactic sequences
    - Multiple code blocks (takes the first one)
    """
    # Try markdown code block first
    m = re.search(r'```(?:lean)?\s*\n(.*?)\n```', response, re.DOTALL)
    if m:
        return m.group(1).strip()

    # Try indented block (all lines starting with spaces after a blank line)
    lines = response.strip().splitlines()
    tactic_lines = []
    for line in lines:
        stripped = line.strip()
        # Skip empty lines and explanatory text
        if not stripped:
            if tactic_lines:
                break  # End of tactic block
            continue
        # Skip lines that look like natural language
        if stripped.startswith("#") or stripped.startswith("//"):
            continue
        tactic_lines.append(line)

    if tactic_lines:
        return "\n".join(tactic_lines).strip()

    # Fallback: return the whole response
    return response.strip()


def apply_tactic_to_file(filepath: str, line: int, tactic: str,
                          backup: bool = True) -> str:
    """Replace sorry at the given line with the tactic.

    Returns the path to the backup file (if created).

    The replacement is simple: find `sorry` on the given line and replace
    it with the tactic. For multi-line tactics, the indentation of the
    sorry is used for subsequent lines.
    """
    path = Path(filepath)
    content = path.read_text()
    lines = content.splitlines(keepends=True)

    # Create backup
    backup_path = ""
    if backup:
        backup_path = str(path) + ".sorry_backup"
        shutil.copy2(path, backup_path)
        logger.info(f"Backup: {backup_path}")

    # Find and replace sorry on the target line (0-indexed internally, 1-indexed input)
    target_idx = line - 1
    if target_idx < 0 or target_idx >= len(lines):
        raise ValueError(f"Line {line} out of range (file has {len(lines)} lines)")

    target_line = lines[target_idx]
    sorry_match = re.search(r'\bsorry\b', target_line)
    if not sorry_match:
        raise ValueError(f"No sorry found on line {line}: {target_line.rstrip()}")

    # Get indentation of sorry
    indent = " " * sorry_match.start()

    # Format multi-line tactic with proper indentation
    tactic_lines = tactic.splitlines()
    if len(tactic_lines) == 1:
        # Single-line: direct replacement
        replacement = target_line[:sorry_match.start()] + tactic + target_line[sorry_match.end():]
        lines[target_idx] = replacement
    else:
        # Multi-line: first line replaces sorry, subsequent lines are indented
        first = target_line[:sorry_match.start()] + tactic_lines[0]
        rest = [indent + "  " + tl for tl in tactic_lines[1:]]
        replacement = first + "\n" + "\n".join(rest) + target_line[sorry_match.end():]
        lines[target_idx] = replacement

    path.write_text("".join(lines))
    logger.info(f"Replaced sorry at {filepath}:{line} with tactic ({len(tactic_lines)} lines)")
    return backup_path


def restore_backup(filepath: str, backup_path: str) -> None:
    """Restore the backup file (undo the tactic application)."""
    if backup_path and Path(backup_path).exists():
        shutil.copy2(backup_path, filepath)
        Path(backup_path).unlink()
        logger.info(f"Restored backup: {filepath}")


def check_proof(project_dir: str, module: Optional[str] = None,
                lake_cmd: str = "lake", timeout: int = 300) -> tuple[bool, str]:
    """Run `lake build` to check if the proof is accepted.

    Returns (success, error_output).
    Success = build completes without errors for the relevant module.
    """
    cmd = [lake_cmd, "build"]
    if module:
        cmd.append(module)

    logger.info(f"Checking proof: {' '.join(cmd)}")

    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            cwd=project_dir,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return False, "Build timed out"

    output = result.stdout + result.stderr

    # Check for errors (not warnings)
    has_errors = bool(re.search(r'(?:^|\n)\s*error:', output))
    # Check for remaining sorry warnings
    has_sorry = bool(re.search(r"declaration uses .sorry.", output))

    if has_errors:
        # Extract just the error lines for feedback
        error_lines = [l for l in output.splitlines()
                       if 'error:' in l.lower() or 'type mismatch' in l.lower()]
        error_msg = "\n".join(error_lines[:10])  # Limit error output
        return False, error_msg

    if has_sorry:
        return False, "Proof still contains sorry"

    return True, ""


def apply_and_check(goal: SorryGoal, tactic: str,
                     project_dir: str,
                     module: Optional[str] = None,
                     lake_cmd: str = "lake") -> ProofResult:
    """Apply a tactic to a sorry location and check with lake build.

    This is a single attempt. The retry loop is in the caller.
    """
    backup_path = ""
    try:
        # Apply tactic
        backup_path = apply_tactic_to_file(goal.file, goal.line, tactic)

        # Check with lake build
        success, error = check_proof(project_dir, module, lake_cmd)

        if success:
            # Remove backup on success
            if backup_path:
                Path(backup_path).unlink(missing_ok=True)
            return ProofResult(goal=goal, success=True, tactic=tactic, attempts=1)
        else:
            # Restore backup on failure
            restore_backup(goal.file, backup_path)
            return ProofResult(goal=goal, success=False, tactic=tactic,
                              error=error, attempts=1)
    except Exception as e:
        # Restore backup on any error
        if backup_path:
            restore_backup(goal.file, backup_path)
        return ProofResult(goal=goal, success=False, tactic=tactic,
                          error=str(e), attempts=1)


# Mock LLM: returns pre-written proofs for known goals
MOCK_PROOFS = {
    # Test proofs
    "test_trivial": "trivial",
    "test_and": "exact ⟨trivial, trivial⟩",
    "test_hyp": "omega",
    # Simple validHoare for rb_size (read-only, returns count)
    "rb_size_spec_sat": "intro s hp; exact sorry",
    # Simple validHoare for rb_capacity (read-only, returns capacity)
    "rb_capacity_spec_sat": "intro s hp; exact sorry",
}


def mock_llm(goal: SorryGoal, prompt: str) -> str:
    """Mock LLM that returns pre-written proofs for known goals.

    This demonstrates the architecture without requiring a live LLM.
    Falls back to `sorry` for unknown goals.
    """
    name = goal.enclosing_name or ""
    for key, proof in MOCK_PROOFS.items():
        if key in name:
            logger.info(f"Mock LLM: found pre-written proof for {key}")
            return proof

    logger.info(f"Mock LLM: no pre-written proof for {name}, returning sorry")
    return "sorry"


if __name__ == "__main__":
    import sys
    logging.basicConfig(level=logging.INFO)
    print("apply_proof.py: use via clift-prove-by-claudecode CLI")
