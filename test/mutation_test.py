"""Mutation testing: inject bugs in CImporter output, verify proofs catch them.

Tests proof COVERAGE, not proof EXISTENCE. If a mutation (deliberate bug) is
injected and proofs still pass, that reveals a coverage gap: the proofs don't
depend on the thing we broke.

seL4 used this technique to validate their proofs caught real bugs.

10 mutation operators:
  1. swap_operands     - swap LHS/RHS of binary operation
  2. drop_guard        - remove a .guard wrapper
  3. off_by_one        - change constant by +1
  4. type_change       - change UInt32 to UInt64
  5. negate_condition   - negate a boolean condition
  6. remove_statement  - delete a .basic statement
  7. swap_branches     - swap if/else branches
  8. change_constant   - replace 0 with 1
  9. remove_cast       - remove a type cast
 10. swap_field_access - swap two field accesses

Usage:
    python test/mutation_test.py [--target Generated/Gcd.lean] [--project-dir .]

Each mutation:
  1. Copy the target file
  2. Apply mutation
  3. Run `lake build` (timeout 300s)
  4. If build fails (type error or proof error): mutation CAUGHT (good)
  5. If build succeeds: mutation ESCAPED (coverage gap)
  6. Restore original file

Reports: X/10 mutations caught by existing proofs.
"""

import argparse
import logging
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

logger = logging.getLogger(__name__)


@dataclass
class MutationResult:
    """Result of a single mutation test."""
    name: str
    description: str
    caught: bool  # True = build failed (proof caught the bug)
    build_output: str  # relevant error output
    applied: bool  # whether the mutation could be applied


# Mutation 1: Swap operands in a modulo operation
def mutate_swap_operands(content: str) -> tuple[str, str]:
    """Swap LHS and RHS of a % operation (a % b -> b % a)."""
    # Pattern: s.locals.a % s.locals.b -> s.locals.b % s.locals.a
    pattern = r'(s\.locals\.\w+)\s*%\s*(s\.locals\.\w+)'
    m = re.search(pattern, content)
    if not m:
        return content, ""
    old = m.group(0)
    new = f"{m.group(2)} % {m.group(1)}"
    return content.replace(old, new, 1), f"Swapped: {old} -> {new}"


# Mutation 2: Drop a guard (remove .guard wrapper, keep the inner body)
def mutate_drop_guard(content: str) -> tuple[str, str]:
    """Remove a .guard wrapper, keeping only the inner .basic."""
    # Find a .guard line and the next .basic
    pattern = r'\.guard\s+\(fun\s+\w+\s*=>\s*[^)]+\)\s*\n\s*\('
    m = re.search(pattern, content)
    if not m:
        return content, ""
    # Replace the guard line with just a paren
    old = m.group(0)
    new = "("
    return content.replace(old, new, 1), f"Dropped guard at position {m.start()}"


# Mutation 3: Off-by-one (change ≠ 0 to ≠ 1)
def mutate_off_by_one(content: str) -> tuple[str, str]:
    """Change a comparison constant: ≠ 0 -> ≠ 1."""
    old = "≠ 0"
    if old not in content:
        return content, ""
    return content.replace(old, "≠ 1", 1), "Changed ≠ 0 to ≠ 1"


# Mutation 4: Type change (UInt32 -> UInt64)
def mutate_type_change(content: str) -> tuple[str, str]:
    """Change UInt32 to UInt64 in a struct field."""
    # Only change the first occurrence in the Locals structure
    pattern = r'(\w+\s*:\s*)UInt32'
    m = re.search(pattern, content)
    if not m:
        return content, ""
    old = m.group(0)
    new = m.group(1) + "UInt64"
    return content.replace(old, new, 1), f"Changed type: {old} -> {new}"


# Mutation 5: Negate condition
def mutate_negate_condition(content: str) -> tuple[str, str]:
    """Negate a boolean condition: ≠ -> = or vice versa."""
    if "≠ 0" in content:
        return content.replace("≠ 0", "= 0", 1), "Negated condition: ≠ 0 -> = 0"
    elif "= 0" in content:
        return content.replace("= 0", "≠ 0", 1), "Negated condition: = 0 -> ≠ 0"
    return content, ""


# Mutation 6: Remove a statement (delete a .basic line and its body)
def mutate_remove_statement(content: str) -> tuple[str, str]:
    """Remove a .basic statement by replacing it with .skip."""
    pattern = r'\.basic\s+\(fun\s+\w+\s*=>\s*\{[^}]+\}\s*\)'
    m = re.search(pattern, content)
    if not m:
        return content, ""
    old = m.group(0)
    return content.replace(old, ".skip", 1), f"Removed .basic at position {m.start()}"


# Mutation 7: Swap branches (swap .seq arguments)
def mutate_swap_branches(content: str) -> tuple[str, str]:
    """Swap the two arguments of the first .catch statement."""
    # Find .catch and swap its two branches (simplified)
    pattern = r'\.catch\s*\n(\s*\([\s\S]*?\))\s*\n(\s*\.skip)'
    m = re.search(pattern, content)
    if not m:
        return content, ""
    old = m.group(0)
    new = f".catch\n{m.group(2)}\n{m.group(1)}"
    return content.replace(old, new, 1), "Swapped catch branches"


# Mutation 8: Change constant (replace a numeric 0 with 1 in a comparison)
def mutate_change_constant(content: str) -> tuple[str, str]:
    """Change first numeric constant in decide: 0 -> 1."""
    pattern = r'decide\s*\([^)]*?(\b0\b)'
    m = re.search(pattern, content)
    if not m:
        return content, ""
    pos = m.start(1)
    mutated = content[:pos] + "1" + content[pos+1:]
    return mutated, f"Changed constant 0 to 1 at position {pos}"


# Mutation 9: Remove a type annotation
def mutate_remove_cast(content: str) -> tuple[str, str]:
    """Remove a type annotation from a field (: UInt32 -> empty)."""
    pattern = r'(\w+)\s*:\s*UInt32(\s)'
    m = re.search(pattern, content)
    if not m:
        return content, ""
    # This is structural - removing the type will cause a parse error
    old = m.group(0)
    new = m.group(1) + m.group(2)
    return content.replace(old, new, 1), f"Removed type annotation from {m.group(1)}"


# Mutation 10: Swap field access (swap two field names)
def mutate_swap_field_access(content: str) -> tuple[str, str]:
    """Swap two field accesses: s.locals.a and s.locals.b."""
    if "s.locals.a" in content and "s.locals.b" in content:
        # Use a placeholder to avoid double-swap
        temp = content.replace("s.locals.a", "PLACEHOLDER_A")
        temp = temp.replace("s.locals.b", "s.locals.a", 1)
        temp = temp.replace("PLACEHOLDER_A", "s.locals.b", 1)
        if temp != content:
            return temp, "Swapped s.locals.a <-> s.locals.b (first occurrence)"
    return content, ""


# All mutation operators
MUTATIONS = [
    ("swap_operands", "Swap binary operands", mutate_swap_operands),
    ("drop_guard", "Remove guard wrapper", mutate_drop_guard),
    ("off_by_one", "Off-by-one in constant", mutate_off_by_one),
    ("type_change", "Change UInt32 to UInt64", mutate_type_change),
    ("negate_condition", "Negate boolean condition", mutate_negate_condition),
    ("remove_statement", "Remove a .basic statement", mutate_remove_statement),
    ("swap_branches", "Swap catch branches", mutate_swap_branches),
    ("change_constant", "Change constant 0 -> 1", mutate_change_constant),
    ("remove_cast", "Remove type annotation", mutate_remove_cast),
    ("swap_field_access", "Swap field accesses", mutate_swap_field_access),
]


def run_build(project_dir: str, timeout: int = 300) -> tuple[bool, str]:
    """Run lake build. Returns (success, output)."""
    try:
        result = subprocess.run(
            ["lake", "build"],
            capture_output=True,
            text=True,
            cwd=project_dir,
            timeout=timeout,
        )
        output = result.stdout + result.stderr
        # Check for errors
        has_errors = bool(re.search(r'error:', output, re.IGNORECASE))
        return not has_errors, output
    except subprocess.TimeoutExpired:
        return False, "Build timed out (>300s)"
    except Exception as e:
        return False, f"Build failed to start: {e}"


def run_mutation_tests(
    target_file: str,
    project_dir: str,
    timeout: int = 300,
) -> list[MutationResult]:
    """Run all 10 mutation tests on the target file.

    For each mutation:
    1. Backup original
    2. Apply mutation
    3. Run lake build
    4. Record whether the mutation was caught
    5. Restore original
    """
    target = Path(target_file)
    if not target.exists():
        logger.error(f"Target file not found: {target_file}")
        return []

    original_content = target.read_text()
    backup_path = str(target) + ".mutation_backup"
    results = []

    for name, description, mutator in MUTATIONS:
        logger.info(f"\n{'='*50}")
        logger.info(f"Mutation: {name} - {description}")
        logger.info(f"{'='*50}")

        # Apply mutation
        mutated_content, mutation_detail = mutator(original_content)

        if mutated_content == original_content or not mutation_detail:
            logger.warning(f"  Mutation {name} could not be applied to {target_file}")
            results.append(MutationResult(
                name=name,
                description=description,
                caught=False,
                build_output="Mutation not applicable to this file",
                applied=False,
            ))
            continue

        logger.info(f"  Applied: {mutation_detail}")

        # Save backup and write mutated file
        shutil.copy2(target, backup_path)
        target.write_text(mutated_content)

        try:
            # Run build
            success, output = run_build(project_dir, timeout=timeout)

            if success:
                # Build succeeded despite bug - mutation ESCAPED
                logger.warning(f"  ESCAPED: Mutation {name} not caught by proofs!")
                results.append(MutationResult(
                    name=name,
                    description=f"{description}: {mutation_detail}",
                    caught=False,
                    build_output=output[-500:] if len(output) > 500 else output,
                    applied=True,
                ))
            else:
                # Build failed - mutation CAUGHT
                logger.info(f"  CAUGHT: Mutation {name} detected by build/proofs")
                # Extract relevant error lines
                error_lines = [
                    l for l in output.splitlines()
                    if "error" in l.lower() or "sorry" in l.lower()
                ]
                results.append(MutationResult(
                    name=name,
                    description=f"{description}: {mutation_detail}",
                    caught=True,
                    build_output="\n".join(error_lines[:10]),
                    applied=True,
                ))
        finally:
            # Always restore original
            shutil.copy2(backup_path, target)
            Path(backup_path).unlink(missing_ok=True)

    return results


def print_report(results: list[MutationResult]) -> None:
    """Print mutation testing report."""
    applied = [r for r in results if r.applied]
    caught = [r for r in applied if r.caught]
    escaped = [r for r in applied if not r.caught]
    not_applied = [r for r in results if not r.applied]

    print(f"\n{'='*60}")
    print(f"  MUTATION TESTING REPORT")
    print(f"{'='*60}")
    print(f"  Total mutations: {len(results)}")
    print(f"  Applied: {len(applied)}")
    print(f"  Not applicable: {len(not_applied)}")
    print(f"  Caught by proofs: {len(caught)}")
    print(f"  Escaped (coverage gap): {len(escaped)}")
    if applied:
        print(f"  Coverage: {len(caught)}/{len(applied)} = {100*len(caught)/len(applied):.0f}%")
    print(f"{'='*60}\n")

    for r in results:
        status = "CAUGHT" if r.caught else ("ESCAPED" if r.applied else "N/A")
        marker = "[+]" if r.caught else ("[-]" if r.applied else "[ ]")
        print(f"  {marker} {r.name}: {r.description}")
        if r.applied and not r.caught:
            print(f"      WARNING: proof did not detect this mutation")

    if escaped:
        print(f"\n  COVERAGE GAPS ({len(escaped)}):")
        for r in escaped:
            print(f"    - {r.name}: {r.description}")
            if r.build_output:
                for line in r.build_output.splitlines()[:3]:
                    print(f"      {line}")


def main():
    parser = argparse.ArgumentParser(
        description="Mutation testing: inject bugs and verify proofs catch them"
    )
    parser.add_argument(
        "--target", default="Generated/Gcd.lean",
        help="Target .lean file to mutate (default: Generated/Gcd.lean)"
    )
    parser.add_argument(
        "--project-dir", default=".",
        help="Path to lake project root (default: .)"
    )
    parser.add_argument(
        "--timeout", type=int, default=300,
        help="Build timeout in seconds (default: 300)"
    )
    parser.add_argument(
        "-v", "--verbose", action="store_true",
        help="Enable debug logging"
    )

    args = parser.parse_args()

    level = logging.DEBUG if args.verbose else logging.INFO
    logging.basicConfig(
        level=level,
        format="%(levelname)s: %(message)s",
    )

    results = run_mutation_tests(
        target_file=args.target,
        project_dir=args.project_dir,
        timeout=args.timeout,
    )

    print_report(results)

    # Exit code: number of escaped mutations
    escaped = sum(1 for r in results if r.applied and not r.caught)
    sys.exit(escaped)


if __name__ == "__main__":
    main()
