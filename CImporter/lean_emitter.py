"""Lean 4 code emitter for the CImporter.

Generates .lean files containing:
  - structure Globals (with rawHeap field)
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
from .c_types import CType, VOID

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
                # Unique type — use plain name
                lean_type = list(types)[0]
                self.all_vars[var_name] = name_to_ctype[var_name][lean_type]
            else:
                # Multiple types — qualify with type suffix
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
        # Must be a type-qualified name — find the type from this function's context
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
        self._w()
        self._w(f"namespace {self.module_name}")
        self._w()

    def _emit_locals(self):
        self._w(f"/-- Local variables (merged from all functions). -/")
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
                # return X => .seq (.basic (set ret__val := X)) .throw
                expr_str = self._emit_expr(stmt.expr, func)
                self._w(f".seq (.basic (fun s => {{ s with locals := {{ s.locals with ret__val := {expr_str} }} }})) .throw")
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
            # If the RHS contains pointer dereferences, emit guards
            deref_guards = self._collect_deref_guards(stmt.value, func)
            if deref_guards:
                for guard_str in deref_guards:
                    self._w(f".guard (fun s => {guard_str})")
                    self._indent += 1
                    self._w("(")
                    self._indent += 1
                self._w(f".basic (fun s => {{ s with locals := {{ s.locals with {field} := {expr_str} }} }})")
                for _ in deref_guards:
                    self._indent -= 1
                    self._w(")")
                    self._indent -= 1
            else:
                self._w(f".basic (fun s => {{ s with locals := {{ s.locals with {field} := {expr_str} }} }})")

        elif stmt.kind == "decl_init":
            # Variable declaration with initializer: same as assignment
            field = self._field_name(stmt.target_var, func)
            expr_str = self._emit_expr(stmt.expr, func)
            deref_guards = self._collect_deref_guards(stmt.expr, func)
            if deref_guards:
                for guard_str in deref_guards:
                    self._w(f".guard (fun s => {guard_str})")
                    self._indent += 1
                    self._w("(")
                    self._indent += 1
                self._w(f".basic (fun s => {{ s with locals := {{ s.locals with {field} := {expr_str} }} }})")
                for _ in deref_guards:
                    self._indent -= 1
                    self._w(")")
                    self._indent -= 1
            else:
                self._w(f".basic (fun s => {{ s with locals := {{ s.locals with {field} := {expr_str} }} }})")

        elif stmt.kind == "deref_write":
            # *p = v  =>  guards for all derefs + .basic (heapUpdate)
            ptr_str = self._emit_expr(stmt.target_expr, func)
            val_str = self._emit_expr(stmt.value, func)
            # Collect guards for the write target AND any derefs in the RHS value
            all_guards = [f"heapPtrValid s.globals.rawHeap {ptr_str}"]
            all_guards.extend(self._collect_deref_guards(stmt.value, func))
            for guard_str in all_guards:
                self._w(f".guard (fun s => {guard_str})")
                self._indent += 1
                self._w("(")
                self._indent += 1
            self._w(f".basic (fun s => {{ s with globals := {{ s.globals with rawHeap := heapUpdate s.globals.rawHeap {ptr_str} {val_str} }} }})")
            for _ in all_guards:
                self._indent -= 1
                self._w(")")
                self._indent -= 1

        elif stmt.kind == "break":
            # break in a while loop: throw (caught by while's internal handling)
            # Note: CSimpl while doesn't have built-in break support.
            # For Phase 1, we'll use throw. This is an approximation.
            self._w(".throw")

        elif stmt.kind == "continue":
            # Similar limitation as break for Phase 1
            self._w(".skip")

        elif stmt.kind == "expr":
            # Expression statement — side-effect only (shouldn't happen in StrictC)
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

            # Comparison operators need special handling — they return Bool in Lean
            if op in ("<", ">", "<=", ">=", "==", "!="):
                # These are handled in bool context by _emit_bool_expr
                # When used as a value (e.g., in ternary), wrap with decide
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

        elif expr.kind == "ternary":
            cond = self._emit_bool_expr(expr.lhs, func)
            true_val = self._emit_expr(expr.rhs, func)
            false_val = self._emit_expr(expr.third, func)
            return f"(if {cond} then {true_val} else {false_val})"

        else:
            raise ValueError(f"Unhandled expression kind: {expr.kind}")

    def _emit_bool_expr(self, expr: Expr, func: FuncInfo) -> str:
        """Emit a Lean Bool expression from a C condition.

        C conditions are integer expressions where 0 = false, non-zero = true.
        Comparison operators naturally produce Bool in Lean.
        """
        if expr.kind == "binop":
            lhs = self._emit_expr(expr.lhs, func)
            rhs = self._emit_expr(expr.rhs, func)
            op = expr.op

            if op in ("<", ">", "<=", ">="):
                lean_op = {"<": "<", ">": ">", "<=": "<=", ">=": ">="}[op]
                return f"decide ({lhs} {lean_op} {rhs})"

            if op == "==":
                return f"decide ({lhs} = {rhs})"

            if op == "!=":
                return f"decide ({lhs} ≠ {rhs})"

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
            return f"decide (s.locals.{field} ≠ 0)"

        if expr.kind == "int_literal":
            return "true" if expr.int_value != 0 else "false"

        # Fallback: treat as integer, compare != 0
        val = self._emit_expr(expr, func)
        return f"decide ({val} ≠ 0)"

    def _collect_deref_guards(self, expr: Expr, func: FuncInfo) -> list[str]:
        """Collect heapPtrValid guard strings for all pointer dereferences in an expression."""
        guards = []
        if expr is None:
            return guards
        if expr.kind == "deref":
            ptr_str = self._emit_expr(expr.operand, func)
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
        return guards

    def _emit_proc_env(self):
        """Emit the procedure environment mapping function names to bodies."""
        self._w("/-- Procedure environment mapping function names to bodies. -/")
        self._w("def procEnv : ProcEnv ProgramState :=")
        self._indent += 1
        if not self.tu.functions:
            self._w("ProcEnv.empty")
        else:
            # Build: ProcEnv.empty |> ProcEnv.insert · "f1" f1_body |> ...
            # Use explicit function application to avoid dot notation issues
            expr = "ProcEnv.empty"
            for func in self.tu.functions:
                expr = f"ProcEnv.insert ({expr}) \"{func.name}\" {func.name}_body"
            self._w(expr)
        self._indent -= 1
