"""Auto-generate projection simp lemmas for L1.modify step functions.

Given a Lean function definition like:
    def swap_f1 (s : ProgramState) : ProgramState := <s.globals, <s.locals.a, s.locals.b, hVal s.globals.rawHeap s.locals.a>>

This generates @[simp] projection lemmas:
    @[simp] theorem swap_f1_globals (s : ProgramState) :
        (swap_f1 s).globals = s.globals := by
      unfold swap_f1; rfl

    @[simp] theorem swap_f1_locals_a (s : ProgramState) :
        (swap_f1 s).locals.a = s.locals.a := by
      unfold swap_f1; rfl

This is string-level analysis of the Lean definition, not MetaM.
The pattern: for each field that appears in the anonymous constructor,
determine what it equals in terms of the input state `s`, and emit a
rfl-based simp lemma.

The [local irreducible] pattern is added for heap-related definitions
(those mentioning hVal or heapUpdate) to prevent kernel deep recursion.

Usage:
    python -m CImporter.proof_engine.gen_projections Examples/SwapProof.lean

    # Or as a library:
    from CImporter.proof_engine.gen_projections import generate_projection_lemmas
    lean_code = generate_projection_lemmas(lean_source)
"""

import re
import logging
from dataclasses import dataclass
from pathlib import Path
from typing import Optional

logger = logging.getLogger(__name__)


@dataclass
class StepFunction:
    """A parsed L1.modify step function definition."""
    name: str
    state_var: str  # typically "s"
    state_type: str  # typically "ProgramState"
    body: str  # the anonymous constructor body
    # Parsed field assignments: {"globals": "s.globals", "locals.a": "s.locals.a", ...}
    field_assignments: dict[str, str]
    uses_heap: bool  # whether body mentions hVal or heapUpdate


@dataclass
class ProjectionLemma:
    """A generated @[simp] projection lemma."""
    func_name: str
    field_path: str  # e.g., "globals" or "locals.a"
    state_var: str
    rhs: str  # what the field equals
    needs_local_irreducible: bool


def _parse_step_functions(lean_source: str) -> list[StepFunction]:
    """Parse step function definitions from Lean source.

    Looks for patterns like:
        private noncomputable def swap_f1 (s : ProgramState) : ProgramState :=
          <...>

    or:
        def swap_f1 (s : ProgramState) : ProgramState :=
          <...>
    """
    results = []

    # Match def with angle-bracket body (anonymous constructor)
    # The definition may span multiple lines until the next def/theorem/private/end
    pattern = re.compile(
        r'(?:private\s+)?(?:noncomputable\s+)?def\s+(\w+)\s+'
        r'\((\w+)\s*:\s*(\w+)\)\s*:\s*\w+\s*:=\s*'
        r'((?:.|\n)*?)(?=\n(?:private |noncomputable |def |theorem |lemma |end |/-|#)|\Z)',
        re.MULTILINE
    )

    for m in pattern.finditer(lean_source):
        name = m.group(1)
        state_var = m.group(2)
        state_type = m.group(3)
        body = m.group(4).strip()

        # Only process functions that return ProgramState and use constructors
        if state_type not in ("ProgramState", "CState"):
            continue
        if not (body.startswith("⟨") or body.startswith("<") or body.startswith("{")):
            continue

        uses_heap = "hVal" in body or "heapUpdate" in body

        # Parse field assignments from the constructor body
        field_assignments = _parse_constructor_fields(body, state_var)

        if field_assignments:
            results.append(StepFunction(
                name=name,
                state_var=state_var,
                state_type=state_type,
                body=body,
                field_assignments=field_assignments,
                uses_heap=uses_heap,
            ))
            logger.info(f"Parsed step function: {name} ({len(field_assignments)} fields)")

    return results


def _parse_constructor_fields(body: str, state_var: str) -> dict[str, str]:
    """Parse anonymous constructor to extract field assignments.

    For a body like:
        ⟨s.globals, ⟨s.locals.a, s.locals.b, hVal s.globals.rawHeap s.locals.a⟩⟩

    Returns:
        {"globals": "s.globals",
         "locals.a": "s.locals.a",
         "locals.b": "s.locals.b",
         "locals.t": "hVal s.globals.rawHeap s.locals.a"}

    This is a simplified parser that handles the two-level structure:
        ⟨globals_expr, ⟨local1, local2, ...⟩⟩
    or:
        ⟨⟨rawHeap_expr⟩, locals_expr⟩
    """
    fields = {}

    # Normalize angle brackets
    normalized = body.replace("⟨", "<").replace("⟩", ">")

    # Try to parse the two-level anonymous constructor
    # Pattern: < outer1, < inner1, inner2, ... > >
    # or: < < inner1 >, outer2 >
    inner = _strip_outer_brackets(normalized)
    if not inner:
        return fields

    # Split at top-level commas (respecting nested brackets)
    top_parts = _split_at_commas(inner)

    if len(top_parts) == 2:
        # Two-level: ⟨globals_part, locals_part⟩
        globals_part = top_parts[0].strip()
        locals_part = top_parts[1].strip()

        # Check which is globals and which is locals
        if globals_part.startswith("<"):
            # Globals is a nested constructor: ⟨⟨rawHeap_expr⟩, locals_expr⟩
            globals_inner = _strip_outer_brackets(globals_part)
            if globals_inner:
                fields["globals.rawHeap"] = globals_inner.strip()
            # locals_part is the whole locals struct
            if locals_part == f"{state_var}.locals":
                pass  # locals unchanged, no projection needed per-field
            else:
                fields["locals"] = locals_part.strip()
        elif locals_part.startswith("<"):
            # Locals is nested: ⟨globals_expr, ⟨l1, l2, ...⟩⟩
            fields["globals"] = globals_part.strip()
            locals_inner = _strip_outer_brackets(locals_part)
            if locals_inner:
                local_parts = _split_at_commas(locals_inner)
                # We don't know field names from the constructor alone,
                # but we can generate indexed projections
                for i, lp in enumerate(local_parts):
                    fields[f"locals_field_{i}"] = lp.strip()
        else:
            # Both are simple: ⟨globals_expr, locals_expr⟩
            fields["globals"] = globals_part.strip()
            fields["locals"] = locals_part.strip()

    return fields


def _strip_outer_brackets(s: str) -> Optional[str]:
    """Remove matching outer < > brackets."""
    s = s.strip()
    if s.startswith("<") and s.endswith(">"):
        return s[1:-1].strip()
    return None


def _split_at_commas(s: str) -> list[str]:
    """Split string at top-level commas, respecting nested < > and ( )."""
    parts = []
    depth = 0
    current = []
    for ch in s:
        if ch in "<(":
            depth += 1
            current.append(ch)
        elif ch in ">)":
            depth -= 1
            current.append(ch)
        elif ch == "," and depth == 0:
            parts.append("".join(current))
            current = []
        else:
            current.append(ch)
    if current:
        parts.append("".join(current))
    return parts


def _generate_lemmas_for_function(func: StepFunction) -> list[ProjectionLemma]:
    """Generate projection lemmas for a single step function."""
    lemmas = []

    for field_path, rhs in func.field_assignments.items():
        # Skip internal indexed fields - we need actual field names
        if field_path.startswith("locals_field_"):
            continue

        lemmas.append(ProjectionLemma(
            func_name=func.name,
            field_path=field_path,
            state_var=func.state_var,
            rhs=rhs,
            needs_local_irreducible=func.uses_heap,
        ))

    return lemmas


def _lemma_to_lean(lemma: ProjectionLemma) -> str:
    """Render a ProjectionLemma as Lean 4 source code."""
    safe_name = lemma.field_path.replace(".", "_")
    theorem_name = f"{lemma.func_name}_{safe_name}"

    # Build the LHS: (func_name s).field_path
    lhs = f"({lemma.func_name} {lemma.state_var}).{lemma.field_path}"
    rhs = lemma.rhs

    lines = []

    if lemma.needs_local_irreducible:
        lines.append(f"@[simp] theorem {theorem_name} ({lemma.state_var} : ProgramState) :")
        lines.append(f"    {lhs} = {rhs} := by")
        lines.append(f"  local irreducible_def hVal heapUpdate")
        lines.append(f"  unfold {lemma.func_name}; rfl")
    else:
        lines.append(f"@[simp] theorem {theorem_name} ({lemma.state_var} : ProgramState) :")
        lines.append(f"    {lhs} = {rhs} := by")
        lines.append(f"  unfold {lemma.func_name}; rfl")

    return "\n".join(lines)


def generate_projection_lemmas(lean_source: str) -> str:
    """Main entry point: given Lean source with step functions, generate all projection lemmas.

    Returns a block of Lean code with @[simp] projection lemmas.
    """
    funcs = _parse_step_functions(lean_source)
    if not funcs:
        logger.info("No step functions found")
        return ""

    sections = []
    sections.append("/-! ## Auto-generated projection simp lemmas")
    sections.append("")
    sections.append("    Generated by CImporter.proof_engine.gen_projections.")
    sections.append("    Each lemma proves that a field of a step function result")
    sections.append("    equals the expected expression, by unfolding and rfl. -/")
    sections.append("")

    for func in funcs:
        lemmas = _generate_lemmas_for_function(func)
        if not lemmas:
            continue

        sections.append(f"-- Projections for {func.name}")
        for lemma in lemmas:
            sections.append(_lemma_to_lean(lemma))
            sections.append("")

    return "\n".join(sections)


def main():
    import sys

    logging.basicConfig(level=logging.INFO)

    if len(sys.argv) < 2:
        print("Usage: python -m CImporter.proof_engine.gen_projections <file.lean>")
        print()
        print("Scans a Lean file for step function definitions (def xxx_f1 ...)")
        print("and generates @[simp] projection lemmas.")
        sys.exit(1)

    filepath = sys.argv[1]
    if not Path(filepath).exists():
        logger.error(f"File not found: {filepath}")
        sys.exit(1)

    source = Path(filepath).read_text()
    output = generate_projection_lemmas(source)

    if output:
        print(output)
    else:
        print("No step functions found in the input file.")
        sys.exit(1)


if __name__ == "__main__":
    main()
