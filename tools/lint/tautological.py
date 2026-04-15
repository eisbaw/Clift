#!/usr/bin/env python3
"""Detect tautological postconditions in FuncSpec definitions.

Scans Lean 4 source files for FuncSpec definitions and flags postconditions
that are trivially true (provable by rfl). Also flags usage of
validHoare_weaken_trivial_post.

Tautological patterns detected:
  1. Direct equality: expr = expr (same expression on both sides)
  2. Let-bound tautology: let x := e; ... x.f = x.f ...
  3. Conjunction of tautologies: x.a = x.a AND x.b = x.b AND ...

Exit code 0 if clean, 1 if any issues found.
"""

import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional


@dataclass
class Finding:
    file: Path
    line: int
    spec_name: str
    kind: str  # "tautological_post", "trivial_weakening"
    detail: str


def _normalize_whitespace(s: str) -> str:
    """Collapse all whitespace to single spaces and strip."""
    return re.sub(r'\s+', ' ', s).strip()


def _is_tautological_eq(lhs: str, rhs: str) -> bool:
    """Check if lhs and rhs are identical expressions (modulo whitespace)."""
    return _normalize_whitespace(lhs) == _normalize_whitespace(rhs)


def _find_funcspec_blocks(content: str, path: Path) -> list[tuple[str, int, str]]:
    """Find FuncSpec definition blocks.

    Returns list of (spec_name, start_line, post_block_text).
    """
    results = []
    lines = content.split('\n')

    # Find lines that start FuncSpec definitions
    # Pattern: def <name> : FuncSpec ...
    funcspec_re = re.compile(
        r'^(?:private\s+)?(?:noncomputable\s+)?def\s+(\w+)\s*:\s*FuncSpec\b'
    )

    for i, line in enumerate(lines):
        stripped = line.lstrip()
        # Skip comments
        if stripped.startswith('--'):
            continue

        m = funcspec_re.match(stripped)
        if not m:
            continue

        spec_name = m.group(1)
        start_line = i + 1  # 1-indexed

        # Find the post := field in the subsequent lines
        # Scan forward from the def line until we hit the next top-level def or end of block
        post_start = None
        post_lines = []
        in_post = False
        brace_depth = 0

        for j in range(i, min(i + 100, len(lines))):
            l = lines[j]
            sl = l.lstrip()

            # Track where blocks
            if 'where' in l and j == i:
                brace_depth = 1

            if in_post:
                # Stop at next field assignment or end of block
                # Fields look like: pre :=, post :=, or a new def at column 0
                if (re.match(r'^(?:private|noncomputable|def|theorem|lemma|/-)', sl)
                        and j > post_start):
                    break
                # Stop at next FuncSpec field (pre := at same or lower indent)
                if re.match(r'^\s{0,2}(pre|post)\s*:=', l) and j > post_start:
                    break
                post_lines.append(l)
            elif re.search(r'\bpost\s*:=', sl):
                post_start = j
                in_post = True
                post_lines.append(l)

        if post_lines:
            post_text = '\n'.join(post_lines)
            results.append((spec_name, start_line, post_text))

    return results


def _check_post_tautological(post_text: str) -> Optional[str]:
    """Check if a postcondition block contains tautological equalities.

    Returns a description of the tautology found, or None.
    """
    # Remove comments
    post_clean = re.sub(r'--[^\n]*', '', post_text)

    # Pattern 1: Direct tautological equality across lines
    # e.g., (hVal s.globals.rawHeap s.locals.rb).count =
    #         (hVal s.globals.rawHeap s.locals.rb).count
    # We look for patterns where a complex expression appears as both LHS and RHS
    # of an equality, possibly spanning two lines.
    taut_findings = []

    # Join lines for multi-line pattern matching
    joined = _normalize_whitespace(post_clean)

    # Find all equality expressions: X = Y
    # We need to be careful about nested parens.
    # Strategy: find all "= " occurrences and check surrounding expressions

    # Pattern 1a: Simple field tautology with same prefix
    # (expr).field = (expr).field  or  var.field = var.field
    eq_pattern = re.compile(
        r'(\([^)]+\)\.\w+|\w+(?:\.\w+)+)\s*=\s*(\([^)]+\)\.\w+|\w+(?:\.\w+)+)'
    )
    for m in eq_pattern.finditer(joined):
        lhs = _normalize_whitespace(m.group(1))
        rhs = _normalize_whitespace(m.group(2))
        if lhs == rhs:
            taut_findings.append(f"tautological equality: {lhs} = {rhs}")

    # Pattern 1b: Let-bound tautology
    # let rb := <expr>; ... rb.field = rb.field
    let_re = re.compile(r'let\s+(\w+)\s*:=\s*([^;]+?)(?:\n|$)')
    for m in let_re.finditer(post_clean):
        var_name = m.group(1)
        # Check for var.field = var.field patterns
        field_taut = re.compile(
            rf'\b{re.escape(var_name)}\.(\w+)\s*=\s*{re.escape(var_name)}\.(\w+)'
        )
        for fm in field_taut.finditer(joined):
            if fm.group(1) == fm.group(2):
                taut_findings.append(
                    f"let-bound tautology: {var_name}.{fm.group(1)} = {var_name}.{fm.group(1)}"
                )

    # Pattern 2: The entire postcondition is only tautologies
    # Remove the "fun r s =>" preamble, "r = Except.ok () ->" guard,
    # and check if remaining conjuncts are all tautologies.

    # Deduplicate: if we found let-bound tautologies, prefer those over
    # the generic "tautological equality" for the same field
    let_bound = {f for f in taut_findings if f.startswith("let-bound")}
    if let_bound:
        # Remove generic findings that duplicate let-bound ones
        let_fields = set()
        for lb in let_bound:
            m = re.search(r'(\w+\.\w+) = \1', lb)
            if m:
                let_fields.add(m.group(1))
        filtered = []
        for f in taut_findings:
            if f.startswith("tautological equality"):
                m = re.search(r'(\w+\.\w+) = \1', f)
                if m and m.group(1) in let_fields:
                    continue
            filtered.append(f)
        taut_findings = filtered

    if taut_findings:
        return "; ".join(sorted(set(taut_findings)))
    return None


def _check_purely_tautological(post_text: str) -> bool:
    """Check if the ENTIRE post (after the Except.ok guard) is tautological.

    This is the worst case: the postcondition proves nothing at all.
    """
    post_clean = re.sub(r'--[^\n]*', '', post_text)
    joined = _normalize_whitespace(post_clean)

    # Remove the preamble: post := fun r s => r = Except.ok () ->
    body_match = re.search(r'Except\.ok\s*\(\)\s*(?:->|→)\s*(.*)', joined)
    if not body_match:
        return False

    body = body_match.group(1).strip()
    if not body:
        return False

    # Remove let bindings for analysis
    body_no_let = re.sub(r'let\s+\w+\s*:=\s*[^;]+', '', body).strip()

    # Split on conjunction
    # Simple split on /\ or ∧
    conjuncts = re.split(r'\s*(?:∧|/\\)\s*', body_no_let)
    conjuncts = [c.strip() for c in conjuncts if c.strip()]

    if not conjuncts:
        return False

    all_taut = True
    for conj in conjuncts:
        # Check if it's an equality X = X
        eq_m = re.match(
            r'^(\([^)]+\)\.\w+|\w+(?:\.\w+)+)\s*=\s*(\([^)]+\)\.\w+|\w+(?:\.\w+)+)$',
            conj
        )
        if eq_m:
            lhs = _normalize_whitespace(eq_m.group(1))
            rhs = _normalize_whitespace(eq_m.group(2))
            if lhs == rhs:
                continue
        all_taut = False
        break

    return all_taut


def _iter_code_lines(content: str):
    """Yield (1-based line number, line text) for non-comment lines only.

    Skips single-line comments (--) and block comments (/- ... -/).
    """
    in_block = False
    for i, line in enumerate(content.split('\n'), 1):
        if in_block:
            if '-/' in line:
                in_block = False
            continue
        if '/-' in line and '-/' not in line:
            in_block = True
            continue
        # Single-line block comment /- ... -/
        if '/-' in line and '-/' in line:
            continue
        stripped = line.lstrip()
        if stripped.startswith('--'):
            continue
        yield i, line


def find_trivial_weakening(content: str, path: Path) -> list[Finding]:
    """Find uses of validHoare_weaken_trivial_post."""
    findings = []
    pattern = re.compile(r'\bvalidHoare_weaken_trivial_post\b')
    # Exclude the definition itself and comments about its removal
    def_re = re.compile(r'(theorem|def)\s+validHoare_weaken_trivial_post')

    for i, line in _iter_code_lines(content):
        code_part = line.split('--')[0] if '--' in line else line
        if pattern.search(code_part) and not def_re.search(line):
            # Skip lines that are clearly documentation/commentary
            if 'REMOVED' in line or 'moved to bogus' in line.lower():
                continue
            findings.append(Finding(
                file=path,
                line=i,
                spec_name="",
                kind="trivial_weakening",
                detail="uses validHoare_weaken_trivial_post",
            ))
    return findings


def scan_file(path: Path) -> list[Finding]:
    """Scan a single Lean file for tautological postconditions."""
    content = path.read_text(errors='replace')
    findings = []

    # Check FuncSpec postconditions
    for spec_name, start_line, post_text in _find_funcspec_blocks(content, path):
        taut = _check_post_tautological(post_text)
        if taut:
            purely = _check_purely_tautological(post_text)
            severity_note = " [ENTIRE post is tautological]" if purely else ""
            findings.append(Finding(
                file=path,
                line=start_line,
                spec_name=spec_name,
                kind="tautological_post",
                detail=f"{taut}{severity_note}",
            ))

    # Check validHoare_weaken_trivial_post usage
    findings.extend(find_trivial_weakening(content, path))

    return findings


def scan_directory(root: Path, dirs: list[str]) -> list[Finding]:
    """Scan Lean files in the given directories."""
    findings = []
    for d in dirs:
        base = root / d
        if not base.is_dir():
            continue
        for p in sorted(base.rglob("*.lean")):
            if "cruft" in p.parts:
                continue
            findings.extend(scan_file(p))
    return findings


def main() -> int:
    # Find project root
    root = Path(__file__).resolve().parent.parent.parent
    if not (root / "lakefile.lean").exists():
        root = Path.cwd()
        while root != root.parent:
            if (root / "lakefile.lean").exists():
                break
            root = root.parent
        else:
            print("ERROR: Could not find project root (no lakefile.lean)", file=sys.stderr)
            return 2

    dirs = ["Examples", "Clift"]
    findings = scan_directory(root, dirs)

    if not findings:
        print("OK: No tautological postconditions found")
        return 0

    # Group by kind
    taut_posts = [f for f in findings if f.kind == "tautological_post"]
    weakening = [f for f in findings if f.kind == "trivial_weakening"]

    print("=== Tautological Postcondition Lint ===")
    print()

    if taut_posts:
        print(f"  WARN: {len(taut_posts)} FuncSpec(s) with tautological postcondition(s):")
        for f in taut_posts:
            rel = f.file.relative_to(root)
            print(f"    {rel}:{f.line}: {f.spec_name}")
            print(f"      {f.detail}")
        print()

    if weakening:
        print(f"  WARN: {len(weakening)} use(s) of validHoare_weaken_trivial_post:")
        for f in weakening:
            rel = f.file.relative_to(root)
            print(f"    {rel}:{f.line}: {f.detail}")
        print()

    total = len(findings)
    print(f"=== {total} issue(s) found ===")
    return 1


if __name__ == "__main__":
    sys.exit(main())
