"""Lean 4 code emitter for the CImporter.

Generates .lean files containing:
  - Lean 4 structures for C structs with CType/MemType instances
  - structure Locals (merged from all functions)
  - abbrev CState := CState Locals (using the library's generic CState)
  - def <func>_body : CSimpl ProgramState for each function
  - def procEnv : ProcEnv ProgramState

Output must compile when imported alongside Clift.CSemantics.

This module is in the TCB. Incorrect emission invalidates all proofs.

Key pattern (from hand-written MaxProof.lean):
  - return X  =>  .seq (.basic (fun s => { s with ret_val := X })) .throw
  - Function body wrapped in .catch ... .skip to convert throw -> normal
  - Conditions use (fun s => decide (expr)) : State -> Bool
  - Assignments use .basic (fun s => { s with field := expr })
"""

import logging
from typing import Optional

from .ast_parser import TranslationUnit, FuncInfo, VarInfo, Stmt, Expr
from .c_types import CType, StructDef, VOID, get_struct_defs

log = logging.getLogger(__name__)


def emit_lean(tu: TranslationUnit, module_name: str) -> str:
    """Generate a complete .lean file from a TranslationUnit.

    Args:
        tu: The parsed translation unit.
        module_name: The Lean module name (e.g. "Max", "Gcd").

    Returns:
        The complete .lean file content as a string.
    """
    emitter = LeanEmitter(tu, module_name)
    return emitter.emit()


class LeanEmitter:
    """Stateful emitter that builds up a .lean file."""

    def __init__(self, tu: TranslationUnit, module_name: str):
        self.tu = tu
        self.module_name = module_name
        self.lines: list[str] = []
        self._indent = 0

        # Collect all variables (params + locals) from all functions,
        # merging same-name same-type into one field.
        self.all_vars: dict[str, CType] = {}  # field_name -> CType
        self._collect_all_vars()

    def _collect_all_vars(self):
        """Merge all params and locals from all functions.

        Same-name, same-type locals share a field.
        Same-name, different-type locals get type-qualified names.
        """
        # First pass: collect all (name, type) pairs
        name_types: dict[str, set[str]] = {}  # var_name -> set of desugared type names
        name_to_ctype: dict[str, dict[str, CType]] = {}  # var_name -> {lean_type -> CType}

        for func in self.tu.functions:
            for var in func.params + func.locals:
                if var.name not in name_types:
                    name_types[var.name] = set()
                    name_to_ctype[var.name] = {}
                name_types[var.name].add(var.c_type.lean_type)
                name_to_ctype[var.name][var.c_type.lean_type] = var.c_type

            # Add ret_val for the return type
            if func.return_type != VOID:
                rname = "ret__val"
                if rname not in name_types:
                    name_types[rname] = set()
                    name_to_ctype[rname] = {}
                name_types[rname].add(func.return_type.lean_type)
                name_to_ctype[rname][func.return_type.lean_type] = func.return_type

        # Second pass: generate field names
        for var_name, types in name_types.items():
            if len(types) == 1:
                # Unique type -- use plain name
                lean_type = list(types)[0]
                self.all_vars[var_name] = name_to_ctype[var_name][lean_type]
            else:
                # Multiple types -- qualify with type suffix
                for lean_type, ctype in name_to_ctype[var_name].items():
                    qualified = f"{var_name}_{lean_type.lower()}"
                    self.all_vars[qualified] = ctype
                    log.warning(
                        "Variable '%s' has multiple types, using qualified name '%s'",
                        var_name, qualified
                    )

    def _w(self, line: str = ""):
        """Write a line with current indentation."""
        if line:
            self.lines.append("  " * self._indent + line)
        else:
            self.lines.append("")

    def _field_name(self, var_name: str, func: FuncInfo) -> str:
        """Get the Locals field name for a variable in a function."""
        # Check if this var_name is unique-typed across all functions
        if var_name in self.all_vars:
            return var_name
        # Must be a type-qualified name -- find the type from this function's context
        for var in func.params + func.locals:
            if var.name == var_name:
                qualified = f"{var_name}_{var.c_type.lean_type.lower()}"
                if qualified in self.all_vars:
                    return qualified
        # Fallback (shouldn't happen if _collect_all_vars is correct)
        return var_name

    def emit(self) -> str:
        """Generate the complete .lean file."""
        self._emit_header()

        # Emit struct definitions before locals
        for sdef in self.tu.structs:
            self._emit_struct(sdef)
            self._w()

        self._emit_locals()
        self._emit_state_abbrev()
        self._w()

        for func in self.tu.functions:
            self._emit_function(func)
            self._w()

        self._emit_proc_env()

        self._w()
        self._w(f"end {self.module_name}")

        return "\n".join(self.lines) + "\n"

    def _emit_header(self):
        self._w(f"-- Generated by CImporter from clang JSON AST. Do not edit.")
        self._w(f"-- Source module: {self.module_name}")
        self._w(f"-- Regenerate with: just import test/c_sources/{self.module_name.lower()}.c {self.module_name}")
        self._w()
        self._w("import Clift.CSemantics")
        self._w()
        self._w(f"set_option maxHeartbeats 400000")
        self._w(f"set_option linter.unusedVariables false")
        self._w()
        self._w(f"namespace {self.module_name}")
        self._w()

    def _emit_struct(self, sdef: StructDef):
        """Emit a Lean structure and CType/MemType instances for a C struct."""
        lean_name = sdef.lean_name

        self._w(f"/-- C struct {sdef.name}: size={sdef.total_size}, align={sdef.alignment} -/")
        self._w(f"structure {lean_name} where")
        self._indent += 1
        for f in sdef.fields:
            self._w(f"{f.name} : {f.c_type.lean_type}")
        self._indent -= 1
        # Note: DecidableEq may fail for recursive struct types (e.g. linked lists)
        # so we only derive Repr and Inhabited
        self._w(f"  deriving Repr, Inhabited")
        self._w()

        # CType instance
        self._w(f"instance : CType {lean_name} where")
        self._indent += 1
        self._w(f"size := {sdef.total_size}")
        self._w(f"align := {sdef.alignment}")
        self._w(f"typeTag := \u27e8{sdef.type_tag_id}\u27e9")
        self._w(f"size_pos := by omega")
        self._indent -= 1
        self._w()

        # MemType instance: fromMem/toMem for the struct
        self._emit_struct_memtype(sdef)

    def _emit_struct_memtype(self, sdef: StructDef):
        """Emit MemType instance for a struct.

        The struct is read/written field-by-field at computed offsets.
        We use MemType instances of the field types to read/write each field.
        """
        lean_name = sdef.lean_name

        # fromMem: read each field at its offset
        self._w(f"/-- Read {lean_name} from {sdef.total_size} bytes. -/")
        self._w(f"def {lean_name}.fromBytes (f : Fin {sdef.total_size} \u2192 UInt8) : {lean_name} where")
        self._indent += 1
        for field in sdef.fields:
            field_type = field.c_type.lean_type
            from_fn = self._memtype_from_fn(field.c_type)
            # Read field.size bytes starting at field.offset
            self._w(f"{field.name} := {from_fn} (fun i => f \u27e8{field.offset} + i.val, by omega\u27e9)")
        self._indent -= 1
        self._w()

        # toMem: write each field at its offset, padding bytes are 0
        # Every field gets an explicit if guard, including the last one.
        # Bytes not covered by any field are padding (0).
        self._w(f"/-- Write {lean_name} to {sdef.total_size} bytes. -/")
        self._w(f"def {lean_name}.toBytes (v : {lean_name}) : Fin {sdef.total_size} \u2192 UInt8 := fun i =>")
        self._indent += 1
        else_depth = 0
        for idx, field in enumerate(sdef.fields):
            to_fn = self._memtype_to_fn(field.c_type)
            end = field.offset + field.size
            self._w(f"if h : {field.offset} \u2264 i.val \u2227 i.val < {end} then")
            self._indent += 1
            self._w(f"{to_fn} v.{field.name} \u27e8i.val - {field.offset}, by omega\u27e9")
            self._indent -= 1
            if idx < len(sdef.fields) - 1:
                self._w("else")
                self._indent += 1
                else_depth += 1
            else:
                self._w("else")
                self._indent += 1
                self._w("0  -- padding bytes")
                self._indent -= 1
        # Unwind else indentation
        for _ in range(else_depth):
            self._indent -= 1
        self._indent -= 1  # Close the fun i =>
        self._w()

        # Roundtrip proof: mechanically generated from field layout.
        # Strategy:
        # 1. For each field, emit a helper showing toBytes at that field's byte range
        #    dispatches to the field's toBytes function.
        # 2. Main theorem: unfold fromBytes, rewrite byte slices via helpers,
        #    apply scalar roundtrip lemmas, close with `cases v; rfl`.
        for idx, field in enumerate(sdef.fields):
            to_fn = self._memtype_to_fn(field.c_type)
            roundtrip_fn = self._memtype_roundtrip_fn(field.c_type)
            end = field.offset + field.size
            self._w(f"private theorem {lean_name}.toBytes_{field.name}_byte "
                    f"(v : {lean_name}) (i : Nat) (hi : i < {field.size}) :")
            self._indent += 1
            self._w(f"{lean_name}.toBytes v \u27e8{field.offset} + i, by omega\u27e9 = "
                    f"{to_fn} v.{field.name} \u27e8i, hi\u27e9 := by")
            self._indent += 1
            self._w(f"unfold {lean_name}.toBytes")
            # For fields before this one: show their guard is false via dif_neg
            for prev_idx in range(idx):
                prev_field = sdef.fields[prev_idx]
                prev_end = prev_field.offset + prev_field.size
                self._w(f"rw [dif_neg (show \u00ac({prev_field.offset} \u2264 ({field.offset} + i) "
                        f"\u2227 ({field.offset} + i) < {prev_end}) from by omega)]")
            # This field's guard is true via dif_pos
            self._w(f"rw [dif_pos (show ({field.offset} \u2264 ({field.offset} + i) "
                    f"\u2227 ({field.offset} + i) < {end}) from by omega)]")
            # Close the Fin equality (value may differ by offset arithmetic)
            self._w(f"congr 1; apply Fin.ext; simp")
            self._indent -= 2
            self._w()

        self._w(f"/-- Roundtrip: fromBytes (toBytes v) = v. -/")
        self._w(f"theorem {lean_name}.fromBytes_toBytes (v : {lean_name}) :")
        self._indent += 1
        self._w(f"{lean_name}.fromBytes ({lean_name}.toBytes v) = v := by")
        self._indent += 1
        # Build the funext helpers for each field
        for field in sdef.fields:
            from_fn = self._memtype_from_fn(field.c_type)
            to_fn = self._memtype_to_fn(field.c_type)
            self._w(f"have h_{field.name} : (fun i : Fin {field.size} => "
                    f"{lean_name}.toBytes v \u27e8{field.offset} + i.val, by omega\u27e9) = "
                    f"{to_fn} v.{field.name} := by")
            self._indent += 1
            self._w(f"funext \u27e8i, hi\u27e9; exact {lean_name}.toBytes_{field.name}_byte v i hi")
            self._indent -= 1
        # Main proof: unfold fromBytes, rewrite, apply roundtrips
        self._w(f"show {lean_name}.fromBytes ({lean_name}.toBytes v) = v")
        self._w(f"unfold {lean_name}.fromBytes")
        rewrites = ", ".join(f"h_{f.name}" for f in sdef.fields)
        roundtrips = ", ".join(
            self._memtype_roundtrip_fn(f.c_type) + f" v.{f.name}"
            for f in sdef.fields
        )
        self._w(f"rw [{rewrites}, {roundtrips}]")
        self._w(f"cases v; rfl")
        self._indent -= 2
        self._w()

        # MemType instance
        self._w(f"instance : MemType {lean_name} where")
        self._indent += 1
        self._w(f"size := {sdef.total_size}")
        self._w(f"align := {sdef.alignment}")
        self._w(f"typeTag := \u27e8{sdef.type_tag_id}\u27e9")
        self._w(f"size_pos := by omega")
        self._w(f"fromMem := {lean_name}.fromBytes")
        self._w(f"toMem := {lean_name}.toBytes")
        self._w(f"roundtrip := {lean_name}.fromBytes_toBytes")
        self._indent -= 1

    def _memtype_roundtrip_fn(self, ctype: CType) -> str:
        """Get the roundtrip theorem name for a CType (fromBytes(toBytes v) = v)."""
        if ctype.is_pointer:
            return "Ptr.fromBytes_toBytes'"
        if ctype.is_struct:
            return f"{ctype.lean_type}.fromBytes_toBytes"
        lean = ctype.lean_type
        if lean in ("UInt8", "UInt16", "UInt32", "UInt64"):
            return f"{lean}.fromBytes_toBytes'"
        if lean in ("Int8", "Int16", "Int32", "Int64"):
            unsigned = lean.replace("Int", "UInt")
            return f"{unsigned}.fromBytes_toBytes'"
        raise ValueError(f"No roundtrip theorem for type {lean}")

    def _memtype_from_fn(self, ctype: CType) -> str:
        """Get the fromMem/fromBytes function name for a CType."""
        if ctype.is_pointer:
            return "Ptr.fromBytes'"
        if ctype.is_struct:
            return f"{ctype.lean_type}.fromBytes"
        lean = ctype.lean_type
        if lean in ("UInt8", "UInt16", "UInt32", "UInt64"):
            return f"{lean}.fromBytes'"
        if lean in ("Int8", "Int16", "Int32", "Int64"):
            # Signed types: for now, treat same as unsigned (Phase 1 limitation)
            unsigned = lean.replace("Int", "UInt")
            return f"{unsigned}.fromBytes'"
        raise ValueError(f"No fromMem function for type {lean}")

    def _memtype_to_fn(self, ctype: CType) -> str:
        """Get the toMem/toBytes function name for a CType."""
        if ctype.is_pointer:
            return "Ptr.toBytes'"
        if ctype.is_struct:
            return f"{ctype.lean_type}.toBytes"
        lean = ctype.lean_type
        if lean in ("UInt8", "UInt16", "UInt32", "UInt64"):
            return f"{lean}.toBytes'"
        if lean in ("Int8", "Int16", "Int32", "Int64"):
            unsigned = lean.replace("Int", "UInt")
            return f"{unsigned}.toBytes'"
        raise ValueError(f"No toMem function for type {lean}")

    def _emit_locals(self):
        # DESIGN DECISION (task-0060): Uninitialized locals use Lean's Inhabited default
        # (zero-initialization). This is technically unsound -- C locals have indeterminate
        # values until assigned. However:
        #   1. All our current C functions assign locals before use.
        #   2. Many embedded compilers zero-initialize (gcc -O0, most debug builds).
        #   3. Emitting CSimpl.spec for nondet init would require NondetM plumbing in
        #      every proof, making Phase 1 proofs significantly harder.
        #   4. This assumption is in the TCB and documented here.
        # Future: Add a --strict-locals flag to emit CSimpl.spec for nondet init.
        self._w(f"/-- Local variables (merged from all functions).")
        self._w(f"    NOTE: Locals use Inhabited default (zero-init). See task-0060. -/")
        self._w("structure Locals where")
        self._indent += 1
        # Sort for deterministic output
        for field_name in sorted(self.all_vars.keys()):
            ctype = self.all_vars[field_name]
            self._w(f"{field_name} : {ctype.lean_type}")
        self._indent -= 1
        self._w(f"  deriving Repr, DecidableEq, Inhabited")
        self._w()

    def _emit_state_abbrev(self):
        self._w("/-- Program state combining globals and locals. -/")
        self._w("abbrev ProgramState := CState Locals")

    def _emit_function(self, func: FuncInfo):
        """Emit a CSimpl function body definition."""
        fname = func.name

        self._w(f"/-- CSimpl body for {fname}(). -/")
        self._w(f"def {fname}_body : CSimpl ProgramState :=")
        self._indent += 1

        # Function body is wrapped in catch ... .skip
        # The catch converts throw (return) into normal completion
        self._w(".catch")
        self._indent += 1
        self._w("(")
        self._indent += 1

        # Emit the body statements
        self._emit_stmt(func.body, func)

        self._indent -= 1
        self._w(")")
        self._w(".skip")
        self._indent -= 2

    def _emit_stmt(self, stmt: Stmt, func: FuncInfo):
        """Emit a CSimpl term for a statement."""
        if stmt.kind == "compound":
            if not stmt.stmts:
                self._w(".skip")
                return
            # Flatten compound into a sequence of .seq
            # Filter out pure decl_init with no initializer (they're just declarations)
            effective_stmts = []
            for s in stmt.stmts:
                if s.kind == "decl_init" and s.expr is None:
                    continue  # Skip bare declarations (no init)
                effective_stmts.append(s)

            if not effective_stmts:
                self._w(".skip")
                return

            if len(effective_stmts) == 1:
                self._emit_stmt(effective_stmts[0], func)
                return

            # Chain with .seq: seq(s1, seq(s2, seq(s3, s4)))
            self._emit_seq_chain(effective_stmts, func)

        elif stmt.kind == "return":
            if stmt.expr is not None and func.return_type != VOID:
                # return X => guards + .seq (.basic (set ret__val := X)) .throw
                expr_str = self._emit_expr(stmt.expr, func)
                guards = self._collect_all_guards(stmt.expr, func)
                def emit_return():
                    self._w(f".seq (.basic (fun s => {{ s with locals := {{ s.locals with ret__val := {expr_str} }} }})) .throw")
                self._emit_with_guards(guards, emit_return)
            else:
                # return; (void) => .throw
                self._w(".throw")

        elif stmt.kind == "if":
            cond_str = self._emit_expr(stmt.condition, func)
            self._w(f".cond (fun s => {self._emit_bool_expr(stmt.condition, func)})")
            self._indent += 1
            self._w("(")
            self._indent += 1
            self._emit_stmt(stmt.then_body, func)
            self._indent -= 1
            self._w(")")
            if stmt.else_body:
                self._w("(")
                self._indent += 1
                self._emit_stmt(stmt.else_body, func)
                self._indent -= 1
                self._w(")")
            else:
                self._w(".skip")
            self._indent -= 1

        elif stmt.kind == "while":
            self._w(f".while (fun s => {self._emit_bool_expr(stmt.condition, func)})")
            self._indent += 1
            self._w("(")
            self._indent += 1
            self._emit_stmt(stmt.loop_body, func)
            self._indent -= 1
            self._w(")")
            self._indent -= 1

        elif stmt.kind == "assign":
            field = self._field_name(stmt.target_var, func)
            expr_str = self._emit_expr(stmt.value, func)
            guards = self._collect_all_guards(stmt.value, func)
            def emit_assign():
                self._w(f".basic (fun s => {{ s with locals := {{ s.locals with {field} := {expr_str} }} }})")
            self._emit_with_guards(guards, emit_assign)

        elif stmt.kind == "decl_init":
            # Variable declaration with initializer: same as assignment
            field = self._field_name(stmt.target_var, func)
            expr_str = self._emit_expr(stmt.expr, func)
            guards = self._collect_all_guards(stmt.expr, func)
            def emit_decl_init():
                self._w(f".basic (fun s => {{ s with locals := {{ s.locals with {field} := {expr_str} }} }})")
            self._emit_with_guards(guards, emit_decl_init)

        elif stmt.kind == "deref_write":
            # *p = v  =>  guards for all derefs/div/overflow + .basic (heapUpdate)
            ptr_str = self._emit_expr(stmt.target_expr, func)
            val_str = self._emit_expr(stmt.value, func)
            guards = [f"heapPtrValid s.globals.rawHeap {ptr_str}"]
            guards.extend(self._collect_all_guards(stmt.value, func))
            def emit_deref_write():
                self._w(f".basic (fun s => {{ s with globals := {{ s.globals with rawHeap := heapUpdate s.globals.rawHeap {ptr_str} {val_str} }} }})")
            self._emit_with_guards(guards, emit_deref_write)

        elif stmt.kind == "member_write":
            # p->field = val or s.field = val
            if stmt.member_is_arrow:
                ptr_str = self._emit_expr(stmt.member_base_expr, func)
                val_str = self._emit_expr(stmt.value, func)
                guards = [f"heapPtrValid s.globals.rawHeap {ptr_str}"]
                guards.extend(self._collect_all_guards(stmt.value, func))
                def emit_member_write():
                    self._w(f".basic (fun s => {{ s with globals := {{ s.globals with rawHeap := heapUpdate s.globals.rawHeap {ptr_str} ({{ hVal s.globals.rawHeap {ptr_str} with {stmt.member_name} := {val_str} }}) }} }})")
                self._emit_with_guards(guards, emit_member_write)
            else:
                # Direct struct field write (s.field = val) -- not via pointer
                # This would be a local struct variable, which is in locals
                raise StrictCViolation(
                    "Direct struct field assignment (s.field = val) for local structs "
                    "not yet supported. Use pointer access (p->field = val)."
                )

        elif stmt.kind == "break":
            self._w(".throw")

        elif stmt.kind == "continue":
            self._w(".skip")

        elif stmt.kind == "expr":
            self._w(".skip")

        else:
            raise ValueError(f"Unhandled statement kind: {stmt.kind}")

    def _emit_seq_chain(self, stmts: list[Stmt], func: FuncInfo):
        """Emit a chain of .seq from a list of statements."""
        if len(stmts) == 1:
            self._emit_stmt(stmts[0], func)
            return
        if len(stmts) == 2:
            self._w(".seq")
            self._indent += 1
            self._w("(")
            self._indent += 1
            self._emit_stmt(stmts[0], func)
            self._indent -= 1
            self._w(")")
            self._w("(")
            self._indent += 1
            self._emit_stmt(stmts[1], func)
            self._indent -= 1
            self._w(")")
            self._indent -= 1
            return
        # More than 2: seq(first, seq(rest...))
        self._w(".seq")
        self._indent += 1
        self._w("(")
        self._indent += 1
        self._emit_stmt(stmts[0], func)
        self._indent -= 1
        self._w(")")
        self._w("(")
        self._indent += 1
        self._emit_seq_chain(stmts[1:], func)
        self._indent -= 1
        self._w(")")
        self._indent -= 1

    def _emit_expr(self, expr: Expr, func: FuncInfo) -> str:
        """Emit a Lean expression string (inside a state lambda).

        Returns a string like 's.locals.a' or 's.locals.a + s.locals.b'.
        The caller wraps this in the appropriate context.
        """
        if expr.kind == "var_ref":
            field = self._field_name(expr.var_name, func)
            return f"s.locals.{field}"

        elif expr.kind == "int_literal":
            # Check if this literal 0 is used in a pointer context
            # (handled by the caller who knows the context)
            return str(expr.int_value)

        elif expr.kind == "binop":
            lhs = self._emit_expr(expr.lhs, func)
            rhs = self._emit_expr(expr.rhs, func)
            op = expr.op

            # Map C operators to Lean operators
            lean_op = {
                "+": "+", "-": "-", "*": "*", "/": "/", "%": "%",
                "&": "&&&", "|": "|||", "^": "^^^",
                "<<": "<<<", ">>": ">>>",
                "&&": "&&", "||": "||",
            }.get(op, op)

            # Comparison operators need special handling -- they return Bool in Lean
            if op in ("<", ">", "<=", ">=", "==", "!="):
                lean_cmp = {
                    "<": "<", ">": ">", "<=": "<=", ">=": ">=",
                    "==": "==", "!=": "!=",
                }.get(op, op)
                return f"(if {lhs} {lean_cmp} {rhs} then 1 else 0)"

            return f"({lhs} {lean_op} {rhs})"

        elif expr.kind == "unop":
            operand = self._emit_expr(expr.operand, func)
            if expr.op == "!":
                return f"(if {operand} == 0 then 1 else 0)"
            elif expr.op == "-":
                return f"(0 - {operand})"
            elif expr.op == "~":
                return f"(~~~{operand})"
            return f"({expr.op}{operand})"

        elif expr.kind == "deref":
            # Pointer dereference: *p => hVal heap p
            ptr_str = self._emit_expr(expr.operand, func)
            return f"(hVal s.globals.rawHeap {ptr_str})"

        elif expr.kind == "member_access":
            # Struct field access: s.field or p->field
            base_str = self._emit_expr(expr.member_base, func)
            field_name = expr.member_name
            if expr.member_is_arrow:
                # p->field => (hVal heap p).field
                return f"(hVal s.globals.rawHeap {base_str}).{field_name}"
            else:
                # s.field => s.field (direct struct value access)
                return f"{base_str}.{field_name}"

        elif expr.kind == "ternary":
            cond = self._emit_bool_expr(expr.lhs, func)
            true_val = self._emit_expr(expr.rhs, func)
            false_val = self._emit_expr(expr.third, func)
            return f"(if {cond} then {true_val} else {false_val})"

        else:
            raise ValueError(f"Unhandled expression kind: {expr.kind}")

    def _is_pointer_expr(self, expr: Expr, func: FuncInfo) -> bool:
        """Check if an expression has pointer type (heuristic based on variable types)."""
        if expr.kind == "var_ref":
            field = self._field_name(expr.var_name, func)
            if field in self.all_vars:
                return self.all_vars[field].is_pointer
            # Check function params
            for p in func.params:
                if p.name == expr.var_name:
                    return p.c_type.is_pointer
            return False
        if expr.kind == "member_access":
            return False  # Could be pointer, but we'd need type info
        if expr.kind == "int_literal":
            return False
        return False

    def _emit_ptr_aware_expr(self, expr: Expr, func: FuncInfo, is_ptr_context: bool) -> str:
        """Emit an expression, converting literal 0 to Ptr.null in pointer contexts."""
        if is_ptr_context and expr.kind == "int_literal" and expr.int_value == 0:
            return "Ptr.null"
        return self._emit_expr(expr, func)

    def _emit_bool_expr(self, expr: Expr, func: FuncInfo) -> str:
        """Emit a Lean Bool expression from a C condition.

        C conditions are integer expressions where 0 = false, non-zero = true.
        Comparison operators naturally produce Bool in Lean.
        """
        if expr.kind == "binop":
            op = expr.op
            # Check if either side is a pointer for NULL comparisons
            lhs_is_ptr = self._is_pointer_expr(expr.lhs, func)
            rhs_is_ptr = self._is_pointer_expr(expr.rhs, func)
            is_ptr_cmp = lhs_is_ptr or rhs_is_ptr

            lhs = self._emit_ptr_aware_expr(expr.lhs, func, is_ptr_cmp)
            rhs = self._emit_ptr_aware_expr(expr.rhs, func, is_ptr_cmp)

            if op in ("<", ">", "<=", ">="):
                lean_op = {"<": "<", ">": ">", "<=": "<=", ">=": ">="}[op]
                return f"decide ({lhs} {lean_op} {rhs})"

            if op == "==":
                return f"decide ({lhs} = {rhs})"

            if op == "!=":
                return f"decide ({lhs} \u2260 {rhs})"

            if op == "&&":
                lbool = self._emit_bool_expr(expr.lhs, func)
                rbool = self._emit_bool_expr(expr.rhs, func)
                return f"({lbool} && {rbool})"

            if op == "||":
                lbool = self._emit_bool_expr(expr.lhs, func)
                rbool = self._emit_bool_expr(expr.rhs, func)
                return f"({lbool} || {rbool})"

        if expr.kind == "unop" and expr.op == "!":
            inner_bool = self._emit_bool_expr(expr.operand, func)
            return f"(!{inner_bool})"

        if expr.kind == "var_ref":
            field = self._field_name(expr.var_name, func)
            return f"decide (s.locals.{field} \u2260 0)"

        if expr.kind == "int_literal":
            return "true" if expr.int_value != 0 else "false"

        # Fallback: treat as integer, compare != 0
        val = self._emit_expr(expr, func)
        return f"decide ({val} \u2260 0)"

    def _collect_deref_guards(self, expr: Expr, func: FuncInfo) -> list[str]:
        """Collect heapPtrValid guard strings for all pointer dereferences in an expression.

        This includes both explicit *p dereferences and p->field arrow accesses.
        """
        guards = []
        if expr is None:
            return guards
        if expr.kind == "deref":
            ptr_str = self._emit_expr(expr.operand, func)
            guards.append(f"heapPtrValid s.globals.rawHeap {ptr_str}")
        if expr.kind == "member_access" and expr.member_is_arrow:
            # p->field implies dereferencing p
            ptr_str = self._emit_expr(expr.member_base, func)
            guards.append(f"heapPtrValid s.globals.rawHeap {ptr_str}")
        # Recurse into sub-expressions
        if expr.lhs is not None:
            guards.extend(self._collect_deref_guards(expr.lhs, func))
        if expr.rhs is not None:
            guards.extend(self._collect_deref_guards(expr.rhs, func))
        if expr.third is not None:
            guards.extend(self._collect_deref_guards(expr.third, func))
        if expr.operand is not None and expr.kind != "deref":
            guards.extend(self._collect_deref_guards(expr.operand, func))
        if expr.member_base is not None and expr.kind != "member_access":
            guards.extend(self._collect_deref_guards(expr.member_base, func))
        return guards

    def _collect_div_guards(self, expr: Expr, func: FuncInfo) -> list[str]:
        """Collect UB guards for division/modulo by zero.

        For every / and % operation, emit a guard that the divisor is nonzero.
        Division by zero is undefined behavior in C for both signed and unsigned.
        """
        guards = []
        if expr is None:
            return guards
        if expr.kind == "binop" and expr.op in ("/", "%"):
            divisor_str = self._emit_expr(expr.rhs, func)
            guards.append(f"{divisor_str} \u2260 0")
        # Recurse into sub-expressions
        if expr.lhs is not None:
            guards.extend(self._collect_div_guards(expr.lhs, func))
        if expr.rhs is not None:
            guards.extend(self._collect_div_guards(expr.rhs, func))
        if expr.third is not None:
            guards.extend(self._collect_div_guards(expr.third, func))
        if expr.operand is not None:
            guards.extend(self._collect_div_guards(expr.operand, func))
        if expr.member_base is not None:
            guards.extend(self._collect_div_guards(expr.member_base, func))
        return guards

    def _collect_signed_overflow_guards(self, expr: Expr, func: FuncInfo) -> list[str]:
        """Collect UB guards for signed integer overflow.

        Signed overflow is UB in C. For every signed +, -, * operation, guard that
        the result is in [INT_MIN, INT_MAX] for the appropriate bit width.
        Also guards INT_MIN / -1 for signed division.

        Uses result_type propagated from the clang AST to determine signedness.
        """
        guards = []
        if expr is None:
            return guards

        if expr.kind == "binop" and expr.result_type is not None and expr.result_type.signed:
            bits = expr.result_type.bits
            if bits > 0:
                int_min = -(2 ** (bits - 1))
                int_max = 2 ** (bits - 1) - 1

                if expr.op in ("+", "-", "*"):
                    # Guard: INT_MIN <= result <= INT_MAX
                    # Use toBitVec.toInt for signed interpretation of UInt values.
                    # UInt32.toBitVec.toInt gives the two's complement signed value.
                    lhs_str = self._emit_expr(expr.lhs, func)
                    rhs_str = self._emit_expr(expr.rhs, func)
                    lean_op = {"+": "+", "-": "-", "*": "*"}[expr.op]
                    guards.append(
                        f"{int_min} \u2264 ({lhs_str}).toBitVec.toInt {lean_op} ({rhs_str}).toBitVec.toInt "
                        f"\u2227 ({lhs_str}).toBitVec.toInt {lean_op} ({rhs_str}).toBitVec.toInt \u2264 {int_max}"
                    )

                elif expr.op == "/":
                    # Signed division: INT_MIN / -1 is UB (result overflows)
                    lhs_str = self._emit_expr(expr.lhs, func)
                    rhs_str = self._emit_expr(expr.rhs, func)
                    # Guard: not (lhs == INT_MIN and rhs == -1)
                    # We express INT_MIN as a bit pattern for the UInt type
                    # Since we map signed to unsigned in Lean, INT_MIN as UInt is 2^(bits-1)
                    uint_int_min = 2 ** (bits - 1)
                    # -1 as unsigned is 2^bits - 1
                    uint_neg_one = 2 ** bits - 1
                    guards.append(
                        f"\u00ac({lhs_str} = {uint_int_min} \u2227 {rhs_str} = {uint_neg_one})"
                    )

        # Recurse into sub-expressions
        if expr.lhs is not None:
            guards.extend(self._collect_signed_overflow_guards(expr.lhs, func))
        if expr.rhs is not None:
            guards.extend(self._collect_signed_overflow_guards(expr.rhs, func))
        if expr.third is not None:
            guards.extend(self._collect_signed_overflow_guards(expr.third, func))
        if expr.operand is not None:
            guards.extend(self._collect_signed_overflow_guards(expr.operand, func))
        if expr.member_base is not None:
            guards.extend(self._collect_signed_overflow_guards(expr.member_base, func))
        return guards

    def _collect_all_guards(self, expr: Expr, func: FuncInfo) -> list[str]:
        """Collect all UB guards for an expression: deref, division, signed overflow."""
        guards = []
        if expr is None:
            return guards
        guards.extend(self._collect_deref_guards(expr, func))
        guards.extend(self._collect_div_guards(expr, func))
        guards.extend(self._collect_signed_overflow_guards(expr, func))
        return guards

    def _emit_with_guards(self, guards: list[str], inner_emit):
        """Emit guard wrappers around an inner emission.

        Args:
            guards: List of guard condition strings.
            inner_emit: Callable that emits the guarded statement.
        """
        if guards:
            for guard_str in guards:
                self._w(f".guard (fun s => {guard_str})")
                self._indent += 1
                self._w("(")
                self._indent += 1
            inner_emit()
            for _ in guards:
                self._indent -= 1
                self._w(")")
                self._indent -= 1
        else:
            inner_emit()

    def _emit_proc_env(self):
        """Emit the procedure environment mapping function names to bodies."""
        self._w("/-- Procedure environment mapping function names to bodies. -/")
        self._w("def procEnv : ProcEnv ProgramState :=")
        self._indent += 1
        if not self.tu.functions:
            self._w("ProcEnv.empty")
        else:
            expr = "ProcEnv.empty"
            for func in self.tu.functions:
                expr = f"ProcEnv.insert ({expr}) \"{func.name}\" {func.name}_body"
            self._w(expr)
        self._indent -= 1
