"""Auto-generate step functions and projection simp lemmas from Generated/*.lean files.

Given a Generated file (e.g., Generated/Swap.lean), this script:
1. Parses the Locals struct to get field names and types
2. Finds each .basic lambda (the modify steps) in function bodies
3. Generates for each step:
   - A `private noncomputable def stepN` using anonymous constructors
   - A `stepN_locals_eq` or `stepN_globals_eq` theorem (first-level projection)
   - Per-field @[simp] projection lemmas (second-level, via rw)
   - A `stepN_funext` theorem matching the original lambda

The two-step projection pattern avoids kernel depth issues on large Locals structs:
  Layer 1: (step s).locals = <f1, ..., fN>  -- by show + rfl on anonymous ctor
  Layer 2: (step s).locals.field = expr      -- by rw [step_locals_eq]

Usage:
    python -m CImporter.proof_engine.gen_projections Generated/Swap.lean
    python -m CImporter.proof_engine.gen_projections Generated/Swap.lean -o Generated/SwapProjections.lean
    python -m CImporter.proof_engine.gen_projections Generated/Swap.lean --func-prefix swap
"""

import re
import sys
import logging
import argparse
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional

logger = logging.getLogger(__name__)


@dataclass
class LocalField:
    """A field in the Locals struct."""
    name: str
    type: str


@dataclass
class BasicLambda:
    """A parsed .basic lambda from the Generated file."""
    func_name: str        # e.g., "swap" from swap_body
    step_index: int       # 1-based index within the function
    raw_lambda: str       # the full (fun s => ...) text
    # What kind of update:
    update_kind: str      # "locals" | "globals" | "both"
    # For locals updates: which fields change and to what
    locals_updates: dict  # field_name -> expression (in terms of s)
    # For globals updates: the rawHeap expression
    globals_rawheap_expr: Optional[str]


@dataclass
class ParsedModule:
    """Parsed information from a Generated/*.lean file."""
    namespace: str
    locals_fields: list[LocalField]
    basic_lambdas: list[BasicLambda]


def parse_generated_file(source: str) -> ParsedModule:
    """Parse a Generated/*.lean file to extract namespace, Locals fields, and .basic lambdas."""
    namespace = _parse_namespace(source)
    locals_fields = _parse_locals_struct(source)
    basic_lambdas = _parse_basic_lambdas(source, locals_fields)
    return ParsedModule(
        namespace=namespace,
        locals_fields=locals_fields,
        basic_lambdas=basic_lambdas,
    )


def _parse_namespace(source: str) -> str:
    """Extract the namespace from `namespace Foo`."""
    m = re.search(r'^namespace\s+(\w+)', source, re.MULTILINE)
    if not m:
        raise ValueError("No namespace found in source")
    return m.group(1)


def _parse_locals_struct(source: str) -> list[LocalField]:
    """Parse `structure Locals where` to get field names and types."""
    # Find the structure block
    m = re.search(
        r'structure\s+Locals\s+where\s*\n(.*?)(?:\n\s*deriving|\n\s*\n)',
        source, re.DOTALL
    )
    if not m:
        raise ValueError("No `structure Locals where` found in source")

    fields = []
    for line in m.group(1).split('\n'):
        line = line.strip()
        if not line or line.startswith('--') or line.startswith('deriving'):
            continue
        # Parse "fieldname : Type"
        fm = re.match(r'(\w+)\s*:\s*(.+)', line)
        if fm:
            fields.append(LocalField(name=fm.group(1), type=fm.group(2).strip()))

    return fields


def _parse_basic_lambdas(source: str, locals_fields: list[LocalField]) -> list[BasicLambda]:
    """Find all .basic (fun s => ...) lambdas in function bodies."""
    results = []

    # Find function bodies: def foo_body : CSimpl ProgramState :=
    func_pattern = re.compile(
        r'def\s+(\w+)_body\s*:\s*CSimpl\s+ProgramState\s*:=\s*\n(.*?)(?=\ndef\s|\nend\s)',
        re.DOTALL
    )

    for func_match in func_pattern.finditer(source):
        func_name = func_match.group(1)
        func_body = func_match.group(2)

        # Find all .basic lambdas in this function body
        # Pattern: .basic (fun s => { s with ... })
        # We need to find matching parens after ".basic ("
        step_index = 0
        pos = 0
        while True:
            idx = func_body.find('.basic (fun ', pos)
            if idx == -1:
                break

            # Find the state variable name
            lambda_start = idx + len('.basic (')
            # Extract the full lambda by matching parens
            lambda_text = _extract_balanced_parens(func_body, lambda_start - 1)
            if not lambda_text:
                pos = idx + 1
                continue

            step_index += 1
            parsed = _parse_lambda_body(func_name, step_index, lambda_text, locals_fields)
            if parsed:
                results.append(parsed)

            pos = idx + 1

    return results


def _extract_balanced_parens(text: str, start: int) -> Optional[str]:
    """Extract text from opening '(' at `start` to matching ')'."""
    if start >= len(text) or text[start] != '(':
        return None
    depth = 0
    for i in range(start, len(text)):
        if text[i] == '(':
            depth += 1
        elif text[i] == ')':
            depth -= 1
            if depth == 0:
                return text[start + 1:i]  # inner content without outer parens
    return None


def _parse_lambda_body(
    func_name: str,
    step_index: int,
    lambda_inner: str,
    locals_fields: list[LocalField],
) -> Optional[BasicLambda]:
    """Parse the inner content of a .basic lambda.

    lambda_inner is the content between the outer parens of .basic (...),
    e.g.: fun s => { s with locals := { s.locals with ret__val := 1 } }
    """
    # Extract state variable and body
    m = re.match(r'fun\s+(\w+)\s*=>\s*(.*)', lambda_inner, re.DOTALL)
    if not m:
        return None

    state_var = m.group(1)
    body = m.group(2).strip()

    locals_updates = {}
    globals_rawheap_expr = None
    update_kind = None

    # Pattern 1: { s with locals := { s.locals with field := expr } }
    locals_match = re.match(
        r'\{\s*' + re.escape(state_var) + r'\s+with\s+locals\s*:=\s*'
        r'\{\s*' + re.escape(state_var) + r'\.locals\s+with\s+(.*?)\s*\}\s*\}',
        body, re.DOTALL
    )
    if locals_match:
        update_kind = "locals"
        # Parse field assignments: field1 := expr1, field2 := expr2, ...
        assignments_text = locals_match.group(1)
        locals_updates = _parse_with_assignments(assignments_text, state_var)

    # Pattern 2: { s with globals := { s.globals with rawHeap := expr } }
    globals_match = re.match(
        r'\{\s*' + re.escape(state_var) + r'\s+with\s+globals\s*:=\s*'
        r'\{\s*' + re.escape(state_var) + r'\.globals\s+with\s+rawHeap\s*:=\s*(.*?)\s*\}\s*\}',
        body, re.DOTALL
    )
    if globals_match:
        update_kind = "globals"
        globals_rawheap_expr = globals_match.group(1).strip()

    if not update_kind:
        logger.warning(f"Could not parse .basic lambda in {func_name} step {step_index}: {body[:100]}...")
        return None

    return BasicLambda(
        func_name=func_name,
        step_index=step_index,
        raw_lambda=lambda_inner,
        update_kind=update_kind,
        locals_updates=locals_updates,
        globals_rawheap_expr=globals_rawheap_expr,
    )


def _parse_with_assignments(text: str, state_var: str) -> dict:
    """Parse 'field1 := expr1, field2 := expr2' from a `with` clause.

    Handles nested expressions by tracking bracket/paren depth.
    """
    result = {}
    # Split on top-level `:=` patterns
    # Pattern: fieldname := expr (where expr may contain nested parens etc.)
    pos = 0
    text = text.strip()
    while pos < len(text):
        # Skip whitespace and commas
        while pos < len(text) and text[pos] in ' \t\n,':
            pos += 1
        if pos >= len(text):
            break

        # Read field name
        field_start = pos
        while pos < len(text) and text[pos] not in ' \t\n:':
            pos += 1
        field_name = text[field_start:pos].strip()
        if not field_name:
            break

        # Skip whitespace
        while pos < len(text) and text[pos] in ' \t\n':
            pos += 1

        # Expect :=
        if pos + 1 < len(text) and text[pos:pos+2] == ':=':
            pos += 2
        else:
            break

        # Skip whitespace
        while pos < len(text) and text[pos] in ' \t\n':
            pos += 1

        # Read expression until top-level comma or end
        expr_start = pos
        depth = 0
        while pos < len(text):
            ch = text[pos]
            if ch in '({':
                depth += 1
            elif ch in ')}':
                depth -= 1
                if depth < 0:
                    break
            elif ch == ',' and depth == 0:
                break
            pos += 1

        expr = text[expr_start:pos].strip()
        if field_name and expr:
            result[field_name] = expr

    return result


def generate_projections(module: ParsedModule, func_prefix: Optional[str] = None) -> str:
    """Generate Lean 4 source with step functions and projection lemmas.

    Args:
        module: Parsed module info
        func_prefix: If provided, only generate for functions starting with this prefix
    """
    field_names = [f.name for f in module.locals_fields]
    lines = []

    lines.append(f"-- Auto-generated projection lemmas for {module.namespace}")
    lines.append(f"-- Generated by: python -m CImporter.proof_engine.gen_projections")
    lines.append(f"-- DO NOT EDIT: regenerate with `just gen-projections`")
    lines.append("")
    lines.append(f"import Generated.{module.namespace}")
    lines.append(f"import Clift.Lifting.Pipeline")
    lines.append("")
    lines.append(f"set_option maxHeartbeats 400000")
    lines.append(f"set_option maxRecDepth 4096")
    lines.append("")
    lines.append(f"namespace {module.namespace}.Projections")
    lines.append("")
    lines.append(f"open {module.namespace}")
    lines.append("")

    for bl in module.basic_lambdas:
        if func_prefix and not bl.func_name.startswith(func_prefix):
            continue

        step_name = f"{bl.func_name}_step{bl.step_index}"
        step_lines = _generate_step_function(step_name, bl, field_names, module.namespace)
        if step_lines:
            lines.extend(step_lines)
            lines.append("")

    lines.append(f"end {module.namespace}.Projections")
    return "\n".join(lines)


def _generate_step_function(
    step_name: str,
    bl: BasicLambda,
    field_names: list[str],
    namespace: str,
) -> list[str]:
    """Generate step function + projection lemmas for one .basic lambda."""
    lines = []
    uses_heap = "hVal" in bl.raw_lambda or "heapUpdate" in bl.raw_lambda
    irreducible_attrs = []
    if uses_heap:
        if "hVal" in bl.raw_lambda:
            irreducible_attrs.append("hVal")
        if "heapUpdate" in bl.raw_lambda:
            irreducible_attrs.append("heapUpdate")
        if "heapPtrValid" in bl.raw_lambda:
            irreducible_attrs.append("heapPtrValid")
    irreducible_str = " ".join(irreducible_attrs) if irreducible_attrs else None

    if bl.update_kind == "locals":
        lines.extend(_gen_locals_update(step_name, bl, field_names, irreducible_str))
    elif bl.update_kind == "globals":
        lines.extend(_gen_globals_update(step_name, bl, field_names, irreducible_str))

    return lines


def _gen_locals_update(
    step_name: str,
    bl: BasicLambda,
    field_names: list[str],
    irreducible_str: Optional[str],
) -> list[str]:
    """Generate step function + projections for a locals-only update."""
    lines = []
    sv = "s"  # state variable in generated code

    # Build the anonymous constructor fields for locals
    # For each field: if it's updated, use the new expression; otherwise use s.locals.field
    ctor_fields = []
    for fname in field_names:
        if fname in bl.locals_updates:
            # Replace state var in expression with 's'
            expr = _rewrite_state_var(bl.locals_updates[fname], sv)
            ctor_fields.append(expr)
        else:
            ctor_fields.append(f"{sv}.locals.{fname}")

    locals_ctor = ", ".join(ctor_fields)

    # Step function definition
    lines.append(f"/-- {bl.func_name} step {bl.step_index}: locals update -/")
    lines.append(f"noncomputable def {step_name} ({sv} : ProgramState) : ProgramState :=")
    lines.append(f"  \u27E8{sv}.globals, \u27E8{locals_ctor}\u27E9\u27E9")
    lines.append("")

    # locals_eq theorem (Layer 1)
    attr_prefix = f"attribute [local irreducible] {irreducible_str} in\n" if irreducible_str else ""
    lines.append(f"{attr_prefix}theorem {step_name}_locals_eq ({sv} : ProgramState) :")
    lines.append(f"    ({step_name} {sv}).locals = \u27E8{locals_ctor}\u27E9 := by")
    lines.append(f"  show (\u27E8{sv}.globals, \u27E8{locals_ctor}\u27E9\u27E9 : ProgramState).locals = _; rfl")
    lines.append("")

    # globals projection (unchanged for locals-only update)
    lines.append(f"{attr_prefix}@[simp] theorem {step_name}_globals ({sv} : ProgramState) :")
    lines.append(f"    ({step_name} {sv}).globals = {sv}.globals := by")
    lines.append(f"  show (\u27E8{sv}.globals, \u27E8{locals_ctor}\u27E9\u27E9 : ProgramState).globals = _; rfl")
    lines.append("")

    # Per-field projection lemmas (Layer 2)
    for fname in field_names:
        if fname in bl.locals_updates:
            expr = _rewrite_state_var(bl.locals_updates[fname], sv)
            # If expression involves heap ops, add irreducible attribute
            field_attr = ""
            if irreducible_str and ("hVal" in expr or "heapUpdate" in expr):
                field_attr = f"attribute [local irreducible] {irreducible_str} in\n"
            lines.append(f"{field_attr}@[simp] theorem {step_name}_{fname} ({sv} : ProgramState) :")
            lines.append(f"    ({step_name} {sv}).locals.{fname} = {expr} := by rw [{step_name}_locals_eq]")
        else:
            lines.append(f"@[simp] theorem {step_name}_{fname} ({sv} : ProgramState) :")
            lines.append(f"    ({step_name} {sv}).locals.{fname} = {sv}.locals.{fname} := by rw [{step_name}_locals_eq]")

    lines.append("")

    # funext theorem
    # Reconstruct the original lambda body
    with_parts = ", ".join(f"{fname} := {_rewrite_state_var(bl.locals_updates[fname], sv)}"
                           for fname in bl.locals_updates)
    original_body = f"{{ {sv} with locals := {{ {sv}.locals with {with_parts} }} }}"

    lines.append(f"{attr_prefix}theorem {step_name}_funext :")
    lines.append(f"    (fun {sv} => {original_body}) = {step_name} := by")
    lines.append(f"  funext {sv}; show _ = {step_name} {sv}; unfold {step_name}; rfl")
    lines.append("")

    return lines


def _gen_globals_update(
    step_name: str,
    bl: BasicLambda,
    field_names: list[str],
    irreducible_str: Optional[str],
) -> list[str]:
    """Generate step function + projections for a globals-only (heap) update."""
    lines = []
    sv = "s"
    heap_expr = _rewrite_state_var(bl.globals_rawheap_expr, sv)

    # Step function: ⟨⟨heap_expr⟩, s.locals⟩
    lines.append(f"/-- {bl.func_name} step {bl.step_index}: heap update -/")
    lines.append(f"noncomputable def {step_name} ({sv} : ProgramState) : ProgramState :=")
    lines.append(f"  \u27E8\u27E8{heap_expr}\u27E9, {sv}.locals\u27E9")
    lines.append("")

    attr_prefix = f"attribute [local irreducible] {irreducible_str} in\n" if irreducible_str else ""

    # globals_eq theorem (Layer 1)
    lines.append(f"{attr_prefix}theorem {step_name}_globals_eq ({sv} : ProgramState) :")
    lines.append(f"    ({step_name} {sv}).globals = \u27E8{heap_expr}\u27E9 := by")
    lines.append(f"  show (\u27E8\u27E8{heap_expr}\u27E9, {sv}.locals\u27E9 : ProgramState).globals = _; rfl")
    lines.append("")

    # globals.rawHeap projection
    lines.append(f"{attr_prefix}@[simp] theorem {step_name}_globals_rawHeap ({sv} : ProgramState) :")
    lines.append(f"    ({step_name} {sv}).globals.rawHeap = {heap_expr} := by rw [{step_name}_globals_eq]")
    lines.append("")

    # locals projection (unchanged)
    lines.append(f"{attr_prefix}@[simp] theorem {step_name}_locals ({sv} : ProgramState) :")
    lines.append(f"    ({step_name} {sv}).locals = {sv}.locals := by")
    lines.append(f"  show (\u27E8\u27E8{heap_expr}\u27E9, {sv}.locals\u27E9 : ProgramState).locals = _; rfl")
    lines.append("")

    # Per-field locals projections (all unchanged, via the locals lemma)
    for fname in field_names:
        lines.append(f"@[simp] theorem {step_name}_{fname} ({sv} : ProgramState) :")
        lines.append(f"    ({step_name} {sv}).locals.{fname} = {sv}.locals.{fname} := by rw [{step_name}_locals]")

    lines.append("")

    # funext theorem
    original_body = f"{{ {sv} with globals := {{ {sv}.globals with rawHeap := {heap_expr} }} }}"
    lines.append(f"{attr_prefix}theorem {step_name}_funext :")
    lines.append(f"    (fun {sv} => {original_body}) = {step_name} := by")
    lines.append(f"  funext {sv}; show _ = {step_name} {sv}; unfold {step_name}; rfl")
    lines.append("")

    return lines


def _rewrite_state_var(expr: str, target_var: str) -> str:
    """Rewrite state variable references in an expression.

    The parsed expression uses whatever variable name was in the lambda
    (typically 's'). We normalize to the target_var.
    This is mostly a no-op since Generated files always use 's'.
    """
    return expr


def main():
    parser = argparse.ArgumentParser(
        description="Generate projection simp lemmas from Generated/*.lean files"
    )
    parser.add_argument("input", help="Path to Generated/*.lean file")
    parser.add_argument("-o", "--output", help="Output file path (default: stdout)")
    parser.add_argument("--func-prefix", help="Only process functions with this prefix")
    parser.add_argument("-v", "--verbose", action="store_true", help="Verbose logging")

    args = parser.parse_args()

    logging.basicConfig(level=logging.DEBUG if args.verbose else logging.INFO)

    input_path = Path(args.input)
    if not input_path.exists():
        logger.error(f"File not found: {input_path}")
        sys.exit(1)

    source = input_path.read_text()
    module = parse_generated_file(source)

    logger.info(f"Namespace: {module.namespace}")
    logger.info(f"Locals fields: {[f.name for f in module.locals_fields]}")
    logger.info(f"Basic lambdas found: {len(module.basic_lambdas)}")
    for bl in module.basic_lambdas:
        logger.info(f"  {bl.func_name} step {bl.step_index}: {bl.update_kind} "
                     f"({', '.join(bl.locals_updates.keys()) if bl.locals_updates else 'heap'})")

    output = generate_projections(module, func_prefix=args.func_prefix)

    if args.output:
        Path(args.output).write_text(output)
        logger.info(f"Written to {args.output}")
    else:
        print(output)


if __name__ == "__main__":
    main()
