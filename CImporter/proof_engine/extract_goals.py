"""Extract sorry goals from Lean files.

Two extraction methods:
1. Static: scan .lean files for `sorry` tokens, extract surrounding context
2. Build-based: run `lake build` and parse warning output for sorry locations + goal states

The build-based method is more accurate (gives the actual goal state from Lean's
elaborator) but requires a working build. The static method works without building.
"""

import re
import json
import subprocess
import logging
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Optional

logger = logging.getLogger(__name__)


@dataclass
class SorryGoal:
    """A single sorry location with its context."""
    file: str
    line: int
    col: int
    # Goal state from Lean (if available from build output)
    goal_state: Optional[str] = None
    # Surrounding context (N lines before/after sorry)
    context_before: str = ""
    context_after: str = ""
    # The theorem/def name containing this sorry
    enclosing_name: Optional[str] = None
    # Hypotheses available at the sorry point
    hypotheses: list[str] = None

    def __post_init__(self):
        if self.hypotheses is None:
            self.hypotheses = []

    def to_dict(self) -> dict:
        return asdict(self)


def extract_sorry_static(filepath: str, context_lines: int = 20) -> list[SorryGoal]:
    """Scan a .lean file for sorry tokens. Returns locations + surrounding context.

    This is the fast, no-build-required method. It finds sorry tokens by regex
    and extracts surrounding lines for context. It does NOT provide the actual
    goal state (that requires running Lean's elaborator).

    Args:
        filepath: Path to .lean file
        context_lines: Number of lines before/after sorry to include
    """
    path = Path(filepath)
    if not path.exists():
        logger.warning(f"File not found: {filepath}")
        return []

    lines = path.read_text().splitlines()
    goals = []

    # Find sorry tokens (not in comments or strings)
    for i, line in enumerate(lines):
        # Skip comment lines
        stripped = line.strip()
        if stripped.startswith("--") or stripped.startswith("/-"):
            continue

        # Find sorry (word boundary to avoid matching "sorryAx" etc.)
        for match in re.finditer(r'\bsorry\b', line):
            col = match.start()

            # Extract context
            start = max(0, i - context_lines)
            end = min(len(lines), i + context_lines + 1)
            before = "\n".join(lines[start:i])
            after = "\n".join(lines[i+1:end])

            # Try to find enclosing theorem/def name
            enclosing = _find_enclosing_name(lines, i)

            goals.append(SorryGoal(
                file=str(path),
                line=i + 1,  # 1-indexed
                col=col,
                context_before=before,
                context_after=after,
                enclosing_name=enclosing,
            ))

    return goals


def _find_enclosing_name(lines: list[str], sorry_line: int) -> Optional[str]:
    """Walk backwards from sorry to find the enclosing theorem/def/lemma name."""
    for i in range(sorry_line, -1, -1):
        line = lines[i].strip()
        m = re.match(r'(?:theorem|def|lemma|example|noncomputable def)\s+(\S+)', line)
        if m:
            return m.group(1)
    return None


def extract_sorry_from_build(project_dir: str, module: Optional[str] = None,
                              lake_cmd: str = "lake") -> list[SorryGoal]:
    """Run `lake build` and parse sorry warnings from the output.

    Lean emits warnings like:
      file.lean:42:5: warning: declaration uses `sorry`

    This method captures those warnings and extracts the file/line/col info.
    It also tries to capture goal states if Lean outputs them (varies by version).

    Args:
        project_dir: Path to the lake project root
        module: Optional module name to build (default: build all)
        lake_cmd: Command to invoke lake (may need nix wrapper)
    """
    cmd = [lake_cmd, "build"]
    if module:
        cmd.append(module)

    logger.info(f"Running: {' '.join(cmd)} in {project_dir}")

    result = subprocess.run(
        cmd,
        capture_output=True,
        text=True,
        cwd=project_dir,
        timeout=300,
    )

    output = result.stdout + result.stderr
    goals = []

    # Parse sorry warnings
    # Format: file.lean:line:col: warning: declaration uses `sorry`
    sorry_pattern = re.compile(
        r'(\S+\.lean):(\d+):(\d+):\s+warning:\s+declaration uses .sorry.'
    )

    for match in sorry_pattern.finditer(output):
        filepath = str(Path(project_dir) / match.group(1))
        line = int(match.group(2))
        col = int(match.group(3))

        # Read surrounding context from the file
        static_goals = extract_sorry_static(filepath, context_lines=15)
        # Find the matching static goal (closest line)
        context_goal = None
        for sg in static_goals:
            if abs(sg.line - line) <= 5:
                context_goal = sg
                break

        goal = SorryGoal(
            file=filepath,
            line=line,
            col=col,
            context_before=context_goal.context_before if context_goal else "",
            context_after=context_goal.context_after if context_goal else "",
            enclosing_name=context_goal.enclosing_name if context_goal else None,
        )
        goals.append(goal)

    logger.info(f"Found {len(goals)} sorry locations from build output")
    return goals


def goals_to_json(goals: list[SorryGoal], output_file: Optional[str] = None) -> str:
    """Serialize goals to JSON. Optionally write to file."""
    data = [g.to_dict() for g in goals]
    json_str = json.dumps(data, indent=2)
    if output_file:
        Path(output_file).write_text(json_str)
        logger.info(f"Wrote {len(goals)} goals to {output_file}")
    return json_str


if __name__ == "__main__":
    import sys
    logging.basicConfig(level=logging.INFO)

    if len(sys.argv) < 2:
        print("Usage: python extract_goals.py <file.lean> [--build <project_dir>]")
        sys.exit(1)

    if "--build" in sys.argv:
        idx = sys.argv.index("--build")
        project_dir = sys.argv[idx + 1] if idx + 1 < len(sys.argv) else "."
        goals = extract_sorry_from_build(project_dir)
    else:
        goals = extract_sorry_static(sys.argv[1])

    print(goals_to_json(goals))
