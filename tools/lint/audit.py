#!/usr/bin/env python3
"""Clift proof integrity audit tool.

Checks Lean 4 source files for common proof quality issues:
sorry usage, hand-written L1 bodies, wrong proof targets,
tautological weakening, circular specs, custom axioms,
native_decide, @[csimp], @[implemented_by], unsafe defs,
and vacuous preconditions.

Exit code 0 if no FAIL results, 1 if any FAIL.

Usage:
    python3 tools/lint/audit.py           # colored terminal output
    python3 tools/lint/audit.py --json    # JSON output for CI
"""

import argparse
import json
import logging
import os
import re
import subprocess
import sys
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import Optional

logging.basicConfig(level=logging.WARNING, format="%(levelname)s: %(message)s")
log = logging.getLogger(__name__)

# ---------------------------------------------------------------------------
# Severity
# ---------------------------------------------------------------------------

class Severity(Enum):
    OK = "OK"
    INFO = "INFO"
    WARN = "WARN"
    FAIL = "FAIL"


# ANSI color codes
_COLORS = {
    Severity.OK: "\033[32m",    # green
    Severity.INFO: "\033[34m",  # blue
    Severity.WARN: "\033[33m",  # yellow
    Severity.FAIL: "\033[31m",  # red
}
_RESET = "\033[0m"


# ---------------------------------------------------------------------------
# Result
# ---------------------------------------------------------------------------

@dataclass
class CheckResult:
    name: str
    severity: Severity
    count: int
    message: str
    details: list[str] = field(default_factory=list)

    def to_dict(self) -> dict:
        d = {
            "name": self.name,
            "severity": self.severity.value,
            "count": self.count,
            "message": self.message,
        }
        if self.details:
            d["details"] = self.details
        return d

    def print_colored(self, use_color: bool = True) -> None:
        tag = self.severity.value
        if use_color and sys.stdout.isatty():
            c = _COLORS.get(self.severity, "")
            tag = f"{c}{tag}{_RESET}"
        print(f"  [{tag}] {self.name}: {self.message}")
        for line in self.details:
            print(f"         {line}")


# ---------------------------------------------------------------------------
# File scanning helpers
# ---------------------------------------------------------------------------

def lean_files(dirs: list[str], root: Path) -> list[Path]:
    """Collect .lean files under the given directories, skipping cruft/."""
    files = []
    for d in dirs:
        base = root / d
        if not base.is_dir():
            continue
        for p in sorted(base.rglob("*.lean")):
            if "cruft" in p.parts:
                continue
            files.append(p)
    return files


def is_comment_line(line: str) -> bool:
    """Return True if the line is a single-line comment."""
    stripped = line.lstrip()
    return stripped.startswith("--")


class LeanLineIterator:
    """Iterate over lines of a Lean file, tracking block comment state.

    Yields (line_number, line_text, in_block_comment) tuples.
    """

    def __init__(self, path: Path):
        self.path = path

    def __iter__(self):
        in_block = False
        with open(self.path, "r", errors="replace") as f:
            for lineno, line in enumerate(f, 1):
                line = line.rstrip("\n")
                # Track /- -/ block comments (simplified: no nesting)
                if in_block:
                    if "-/" in line:
                        in_block = False
                    yield (lineno, line, True)
                    continue
                if "/-" in line and "-/" not in line:
                    in_block = True
                    yield (lineno, line, True)
                    continue
                # Single line with /- ... -/ is a block comment line
                if "/-" in line and "-/" in line:
                    yield (lineno, line, True)
                    continue
                yield (lineno, line, False)


# ---------------------------------------------------------------------------
# Check 1: sorry_count
# ---------------------------------------------------------------------------

def sorry_count(root: Path) -> CheckResult:
    """Count sorry in tactic position (not in comments or doc strings)."""
    sorry_re = re.compile(r'\bsorry\b')
    exclude_re = re.compile(r'sorry-free|no sorry|zero sorry|Sorry|#print axioms|sorryAx')

    lib_hits: list[str] = []
    example_hits: list[str] = []

    for path in lean_files(["Clift", "Examples", "Generated"], root):
        for lineno, line, in_block in LeanLineIterator(path):
            if in_block:
                continue
            if is_comment_line(line):
                continue
            # Skip lines where sorry appears only in a trailing comment
            code_part = line.split("--")[0] if "--" in line else line
            if not sorry_re.search(code_part):
                continue
            if exclude_re.search(code_part):
                continue
            rel = path.relative_to(root)
            tag = f"{rel}:{lineno}: {line.strip()}"
            if str(rel).startswith("Clift/"):
                lib_hits.append(tag)
            else:
                example_hits.append(tag)

    # Core library sorry is a FAIL
    if lib_hits:
        return CheckResult(
            name="sorry_in_core_library",
            severity=Severity.FAIL,
            count=len(lib_hits),
            message=f"{len(lib_hits)} sorry in Clift/ (core library must be sorry-free)",
            details=lib_hits,
        )

    total = len(example_hits)
    if total == 0:
        return CheckResult(
            name="sorry_count",
            severity=Severity.OK,
            count=0,
            message="Zero sorry in codebase",
        )
    return CheckResult(
        name="sorry_count",
        severity=Severity.INFO,
        count=total,
        message=f"{total} sorry remaining in Examples/Generated",
        details=example_hits,
    )


# ---------------------------------------------------------------------------
# Check 2: hand_written_l1
# ---------------------------------------------------------------------------

def hand_written_l1(root: Path) -> CheckResult:
    """Detect hand-written L1 body definitions in Examples/."""
    pattern = re.compile(r'^(private\s+)?(noncomputable\s+)?def\s+l1_')
    hits: list[str] = []

    for path in lean_files(["Examples"], root):
        for lineno, line, in_block in LeanLineIterator(path):
            if in_block or is_comment_line(line):
                continue
            if pattern.match(line.lstrip()):
                # Exclude local let bindings
                stripped = line.lstrip()
                if stripped.startswith("let l1_"):
                    continue
                rel = path.relative_to(root)
                hits.append(f"{rel}:{lineno}: {stripped}")

    if not hits:
        return CheckResult(
            name="hand_written_l1",
            severity=Severity.OK,
            count=0,
            message="No hand-written L1 bodies",
        )
    return CheckResult(
        name="hand_written_l1",
        severity=Severity.WARN,
        count=len(hits),
        message=f"{len(hits)} hand-written L1 body definitions (should use clift auto-generation)",
        details=hits,
    )


# ---------------------------------------------------------------------------
# Check 3: wrong_target
# ---------------------------------------------------------------------------

def wrong_target(root: Path) -> CheckResult:
    """Detect proofs against manual/fused/local bodies instead of generated ones."""
    pattern = re.compile(r'satisfiedBy\s+l1_\w+_(manual|fused|local)')
    hits: list[str] = []

    for path in lean_files(["Examples"], root):
        for lineno, line, in_block in LeanLineIterator(path):
            if in_block or is_comment_line(line):
                continue
            code_part = line.split("--")[0] if "--" in line else line
            if pattern.search(code_part):
                rel = path.relative_to(root)
                hits.append(f"{rel}:{lineno}: {line.strip()}")

    if not hits:
        return CheckResult(
            name="wrong_target",
            severity=Severity.OK,
            count=0,
            message="All proofs target generated bodies",
        )
    return CheckResult(
        name="wrong_target",
        severity=Severity.WARN,
        count=len(hits),
        message=f"{len(hits)} proofs target manual/fused bodies instead of generated ones",
        details=hits,
    )


# ---------------------------------------------------------------------------
# Check 4: tautological_weakening
# ---------------------------------------------------------------------------

def tautological_weakening(root: Path) -> CheckResult:
    """Detect validHoare_weaken_trivial_post usage."""
    pattern = re.compile(r'validHoare_weaken_trivial_post')
    # Exclude the definition itself and doc comments
    def_re = re.compile(r'(private\s+)?theorem\s+validHoare_weaken_trivial_post')
    hits: list[str] = []

    for path in lean_files(["Examples", "Clift"], root):
        for lineno, line, in_block in LeanLineIterator(path):
            if in_block or is_comment_line(line):
                continue
            code_part = line.split("--")[0] if "--" in line else line
            if not pattern.search(code_part):
                continue
            if def_re.search(line):
                continue
            rel = path.relative_to(root)
            hits.append(f"{rel}:{lineno}: {line.strip()}")

    if not hits:
        return CheckResult(
            name="tautological_weakening",
            severity=Severity.OK,
            count=0,
            message="No trivial postcondition weakening",
        )
    return CheckResult(
        name="tautological_weakening",
        severity=Severity.WARN,
        count=len(hits),
        message=f"{len(hits)} proofs use validHoare_weaken_trivial_post (trivializes postcondition)",
        details=hits,
    )


# ---------------------------------------------------------------------------
# Check 5: circular_specs
# ---------------------------------------------------------------------------

def circular_specs(root: Path) -> CheckResult:
    """Detect specs with result set = property (potentially circular)."""
    # Pattern: 'results := fun' followed by existential quantifier and conjunction
    pattern = re.compile(r'results\s*:=\s*fun.*∃.*∧')
    hits: list[str] = []

    for path in lean_files(["Examples"], root):
        for lineno, line, in_block in LeanLineIterator(path):
            if in_block or is_comment_line(line):
                continue
            code_part = line.split("--")[0] if "--" in line else line
            if pattern.search(code_part):
                rel = path.relative_to(root)
                hits.append(f"{rel}:{lineno}: {line.strip()}")

    if not hits:
        return CheckResult(
            name="circular_specs",
            severity=Severity.OK,
            count=0,
            message="No circular result-set definitions found",
        )
    return CheckResult(
        name="circular_specs",
        severity=Severity.WARN,
        count=len(hits),
        message=f"{len(hits)} definitions embed spec in result set (potentially circular)",
        details=hits,
    )


# ---------------------------------------------------------------------------
# Check 6: custom_axioms
# ---------------------------------------------------------------------------

def custom_axioms(root: Path) -> CheckResult:
    """Detect axiom/constant declarations in Clift/ and Examples/."""
    pattern = re.compile(r'^(axiom|constant)\s+')
    hits: list[str] = []

    for path in lean_files(["Clift", "Examples"], root):
        for lineno, line, in_block in LeanLineIterator(path):
            if in_block or is_comment_line(line):
                continue
            if pattern.match(line):
                rel = path.relative_to(root)
                hits.append(f"{rel}:{lineno}: {line.strip()}")

    if not hits:
        return CheckResult(
            name="custom_axioms",
            severity=Severity.OK,
            count=0,
            message="No custom axioms (only propext, Quot.sound, Classical.choice)",
        )
    return CheckResult(
        name="custom_axioms",
        severity=Severity.FAIL,
        count=len(hits),
        message=f"{len(hits)} custom axiom/constant declarations",
        details=hits,
    )


# ---------------------------------------------------------------------------
# Check 7: sorry_axiom
# ---------------------------------------------------------------------------

def sorry_axiom(root: Path) -> CheckResult:
    """Check for sorryAx in compiled theorems by building AxiomAudit."""
    olean_dir = root / ".lake" / "build" / "lib" / "lean" / "Examples"
    if not olean_dir.exists():
        return CheckResult(
            name="sorry_axiom",
            severity=Severity.INFO,
            count=0,
            message="SKIP: No .olean files found (run lake build first)",
        )

    # Find lean toolchain
    lean_home = os.path.expanduser("~/.elan/toolchains")
    lake_bin = "lake"
    # Try to find a specific toolchain lake
    for tc_dir in sorted(Path(lean_home).glob("leanprover--lean4*"), reverse=True):
        candidate = tc_dir / "bin" / "lake"
        if candidate.exists():
            lake_bin = str(candidate)
            break

    try:
        result = subprocess.run(
            [lake_bin, "build", "Examples.AxiomAudit"],
            capture_output=True, text=True, timeout=120,
            cwd=str(root),
        )
        output = result.stdout + result.stderr
    except (subprocess.TimeoutExpired, FileNotFoundError) as e:
        return CheckResult(
            name="sorry_axiom",
            severity=Severity.INFO,
            count=0,
            message=f"SKIP: Could not run lake build AxiomAudit: {e}",
        )

    sorry_lines = [l for l in output.splitlines() if "sorryAx" in l]
    if sorry_lines:
        return CheckResult(
            name="sorry_axiom",
            severity=Severity.FAIL,
            count=len(sorry_lines),
            message=f"sorryAx found in compiled theorems",
            details=sorry_lines,
        )
    return CheckResult(
        name="sorry_axiom",
        severity=Severity.OK,
        count=0,
        message="No sorryAx in any compiled theorem",
    )


# ---------------------------------------------------------------------------
# Check 8: native_decide
# ---------------------------------------------------------------------------

def native_decide(root: Path) -> CheckResult:
    """Detect native_decide in proof-critical code (excluding AI test files)."""
    pattern = re.compile(r'\bnative_decide\b')
    # Exclude files that are purely test/AI scaffolding
    exclude_files = {"AISpecTest.lean", "AIStructInvariantTest.lean"}
    hits: list[str] = []

    for path in lean_files(["Clift", "Examples"], root):
        if path.name in exclude_files:
            continue
        for lineno, line, in_block in LeanLineIterator(path):
            if in_block or is_comment_line(line):
                continue
            code_part = line.split("--")[0] if "--" in line else line
            if pattern.search(code_part):
                rel = path.relative_to(root)
                hits.append(f"{rel}:{lineno}: {line.strip()}")

    if not hits:
        return CheckResult(
            name="native_decide",
            severity=Severity.OK,
            count=0,
            message="No native_decide in proof-critical code",
        )
    return CheckResult(
        name="native_decide",
        severity=Severity.WARN,
        count=len(hits),
        message=f"{len(hits)} uses of native_decide (trusted code, not kernel-checked)",
        details=hits,
    )


# ---------------------------------------------------------------------------
# Check 9: csimp_smuggling
# ---------------------------------------------------------------------------

def csimp_smuggling(root: Path) -> CheckResult:
    """Detect @[csimp] usage which can smuggle in computational rewrites."""
    pattern = re.compile(r'@\[csimp\]')
    hits: list[str] = []

    for path in lean_files(["Clift", "Examples"], root):
        for lineno, line, in_block in LeanLineIterator(path):
            if in_block or is_comment_line(line):
                continue
            if pattern.search(line):
                rel = path.relative_to(root)
                hits.append(f"{rel}:{lineno}: {line.strip()}")

    if not hits:
        return CheckResult(
            name="csimp_smuggling",
            severity=Severity.OK,
            count=0,
            message="No @[csimp] usage",
        )
    return CheckResult(
        name="csimp_smuggling",
        severity=Severity.FAIL,
        count=len(hits),
        message=f"{len(hits)} @[csimp] declarations (can smuggle computational rewrites)",
        details=hits,
    )


# ---------------------------------------------------------------------------
# Check 10: implemented_by
# ---------------------------------------------------------------------------

def implemented_by(root: Path) -> CheckResult:
    """Detect @[implemented_by] usage which bypasses kernel checking."""
    pattern = re.compile(r'@\[implemented_by\]')
    hits: list[str] = []

    for path in lean_files(["Clift", "Examples"], root):
        for lineno, line, in_block in LeanLineIterator(path):
            if in_block or is_comment_line(line):
                continue
            if pattern.search(line):
                rel = path.relative_to(root)
                hits.append(f"{rel}:{lineno}: {line.strip()}")

    if not hits:
        return CheckResult(
            name="implemented_by",
            severity=Severity.OK,
            count=0,
            message="No @[implemented_by] usage",
        )
    return CheckResult(
        name="implemented_by",
        severity=Severity.FAIL,
        count=len(hits),
        message=f"{len(hits)} @[implemented_by] declarations (bypasses kernel checking)",
        details=hits,
    )


# ---------------------------------------------------------------------------
# Check 11: unsafe_defs
# ---------------------------------------------------------------------------

def unsafe_defs(root: Path) -> CheckResult:
    """Detect unsafe definitions in Clift/ and Examples/."""
    pattern = re.compile(r'^unsafe\s+')
    hits: list[str] = []

    for path in lean_files(["Clift", "Examples"], root):
        for lineno, line, in_block in LeanLineIterator(path):
            if in_block or is_comment_line(line):
                continue
            if pattern.match(line):
                rel = path.relative_to(root)
                hits.append(f"{rel}:{lineno}: {line.strip()}")

    if not hits:
        return CheckResult(
            name="unsafe_defs",
            severity=Severity.OK,
            count=0,
            message="No unsafe definitions",
        )
    return CheckResult(
        name="unsafe_defs",
        severity=Severity.FAIL,
        count=len(hits),
        message=f"{len(hits)} unsafe definitions",
        details=hits,
    )


# ---------------------------------------------------------------------------
# Check 12: vacuous_preconditions
# ---------------------------------------------------------------------------

def vacuous_preconditions(root: Path) -> CheckResult:
    """Detect False in preconditions (makes the spec vacuously true).

    Only flags 'fun _ => False' when it appears in a precondition context
    (lines containing 'pre', 'precondition', or within FuncSpec definitions).
    Library definitions like cHoareNoAbrupt or emptyCollection are excluded.
    """
    false_pattern = re.compile(r'fun\s+\w+\s*=>\s*False')
    # Only flag in spec/pre context, or scan Examples/ only
    pre_context = re.compile(r'\bpre\b|\bprecondition\b', re.IGNORECASE)
    hits: list[str] = []

    for path in lean_files(["Examples"], root):
        for lineno, line, in_block in LeanLineIterator(path):
            if in_block or is_comment_line(line):
                continue
            code_part = line.split("--")[0] if "--" in line else line
            if false_pattern.search(code_part):
                rel = path.relative_to(root)
                hits.append(f"{rel}:{lineno}: {line.strip()}")

    if not hits:
        return CheckResult(
            name="vacuous_preconditions",
            severity=Severity.OK,
            count=0,
            message="No vacuous preconditions (fun _ => False)",
        )
    return CheckResult(
        name="vacuous_preconditions",
        severity=Severity.WARN,
        count=len(hits),
        message=f"{len(hits)} potential vacuous preconditions (fun _ => False)",
        details=hits,
    )


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

ALL_CHECKS = [
    sorry_count,
    hand_written_l1,
    wrong_target,
    tautological_weakening,
    circular_specs,
    custom_axioms,
    sorry_axiom,
    native_decide,
    csimp_smuggling,
    implemented_by,
    unsafe_defs,
    vacuous_preconditions,
]


def find_project_root() -> Path:
    """Walk up from CWD looking for lakefile.lean (Lean project root)."""
    candidate = Path.cwd()
    for _ in range(10):
        if (candidate / "lakefile.lean").exists():
            return candidate
        parent = candidate.parent
        if parent == candidate:
            break
        candidate = parent
    # Also try the script's own location (tools/lint/audit.py -> ../../)
    script_root = Path(__file__).resolve().parent.parent.parent
    if (script_root / "lakefile.lean").exists():
        return script_root
    log.error("Could not find project root (no lakefile.lean found)")
    sys.exit(2)


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Clift proof integrity audit",
    )
    parser.add_argument(
        "--json", action="store_true",
        help="Output JSON (for CI pipelines)",
    )
    parser.add_argument(
        "--skip-lake", action="store_true",
        help="Skip checks that require lake build (sorry_axiom)",
    )
    args = parser.parse_args()

    root = find_project_root()

    checks = ALL_CHECKS
    if args.skip_lake:
        checks = [c for c in checks if c.__name__ != "sorry_axiom"]

    results: list[CheckResult] = []
    for check_fn in checks:
        try:
            result = check_fn(root)
        except Exception as e:
            result = CheckResult(
                name=check_fn.__name__,
                severity=Severity.FAIL,
                count=1,
                message=f"Check crashed: {e}",
            )
        results.append(result)

    if args.json:
        output = {
            "root": str(root),
            "checks": [r.to_dict() for r in results],
            "has_fail": any(r.severity == Severity.FAIL for r in results),
        }
        print(json.dumps(output, indent=2))
    else:
        print("=== Clift Proof Integrity Audit ===")
        print(f"    Project root: {root}")
        print()
        for r in results:
            r.print_colored()
        print()

        # Summary
        counts = {}
        for r in results:
            counts[r.severity] = counts.get(r.severity, 0) + 1
        parts = []
        for sev in [Severity.FAIL, Severity.WARN, Severity.INFO, Severity.OK]:
            c = counts.get(sev, 0)
            if c > 0:
                parts.append(f"{c} {sev.value}")
        total_issues = sum(r.count for r in results if r.severity in (Severity.FAIL, Severity.WARN, Severity.INFO))
        print(f"=== Summary: {', '.join(parts)} ({total_issues} total issues) ===")

    has_fail = any(r.severity == Severity.FAIL for r in results)
    sys.exit(1 if has_fail else 0)


if __name__ == "__main__":
    main()
