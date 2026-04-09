"""Clang JSON AST parser for the CImporter.

Traverses clang's -ast-dump=json output and extracts:
  - Struct definitions (name, fields, layout)
  - Function declarations (name, return type, parameters)
  - Local variable declarations (name, type)
  - Statement structure (if/else, while, return, assignments, expressions)

This module is in the TCB. Incorrect parsing invalidates all proofs.

StrictC restrictions enforced:
  - No float, goto, longjmp, switch fall-through
  - No address-of locals (&local)
  - No side effects in expressions
  - No variadic functions, VLAs
  - No pre/post increment in expressions (as sub-expressions)
"""

import json
import logging
from dataclasses import dataclass, field
from typing import Optional

from .c_types import (
    CType, parse_clang_type, return_type_from_qual, UnsupportedTypeError,
    StructDef, StructField, compute_struct_layout, register_struct,
    clear_struct_defs, get_struct_defs,
)

log = logging.getLogger(__name__)


class StrictCViolation(Exception):
    """Raised when the C code violates StrictC restrictions."""
    pass


# --- Intermediate representation ---

@dataclass
class VarInfo:
    """A variable (parameter or local)."""
    name: str
    c_type: CType

@dataclass
class Expr:
    """An expression in the C AST."""
    kind: str  # "var_ref", "int_literal", "binop", "unop", "ternary", "deref", "member_access"
    # Fields depend on kind:
    var_name: Optional[str] = None       # for var_ref
    int_value: Optional[int] = None      # for int_literal
    op: Optional[str] = None             # for binop/unop
    lhs: Optional['Expr'] = None         # for binop, ternary (condition)
    rhs: Optional['Expr'] = None         # for binop, ternary (true branch)
    third: Optional['Expr'] = None       # for ternary (false branch)
    operand: Optional['Expr'] = None     # for unop, deref (the pointer expr)
    result_type: Optional[CType] = None  # type of the expression result
    # For member_access (s.field or p->field):
    member_name: Optional[str] = None    # field name
    member_is_arrow: bool = False        # True for p->field (implies deref)
    member_base: Optional['Expr'] = None # the struct/pointer expression

@dataclass
class Stmt:
    """A statement in the C AST."""
    kind: str  # "compound", "return", "if", "while", "assign", "decl_init", "expr",
               # "deref_write", "member_write"
    # Fields depend on kind:
    stmts: list['Stmt'] = field(default_factory=list)  # for compound
    expr: Optional[Expr] = None                         # for return, expr, decl_init value
    condition: Optional[Expr] = None                    # for if, while
    then_body: Optional['Stmt'] = None                  # for if
    else_body: Optional['Stmt'] = None                  # for if
    loop_body: Optional['Stmt'] = None                  # for while
    target_var: Optional[str] = None                    # for assign, decl_init
    value: Optional[Expr] = None                        # for assign, deref_write, member_write
    target_expr: Optional[Expr] = None                  # for deref_write (the pointer being written to)
    # For member_write (p->field = val):
    member_base_expr: Optional[Expr] = None             # the struct/pointer expression
    member_name: Optional[str] = None                   # field name
    member_is_arrow: bool = False                       # True for p->field

@dataclass
class FuncInfo:
    """A function declaration."""
    name: str
    return_type: CType
    params: list[VarInfo]
    locals: list[VarInfo]
    body: Stmt


@dataclass
class TranslationUnit:
    """Parsed translation unit (one .c file)."""
    functions: list[FuncInfo]
    structs: list[StructDef]  # Struct definitions in order


# --- Parser ---

def parse_translation_unit(ast: dict) -> TranslationUnit:
    """Parse a clang JSON AST root node into a TranslationUnit.

    Args:
        ast: The root dict from clang's -ast-dump=json output.

    Returns:
        TranslationUnit with all user-defined functions and structs.
    """
    assert ast.get("kind") == "TranslationUnitDecl", \
        f"Expected TranslationUnitDecl, got {ast.get('kind')}"

    clear_struct_defs()
    structs = []
    functions = []

    for node in ast.get("inner", []):
        # Parse struct definitions first (must come before functions that use them)
        if node.get("kind") == "RecordDecl" and node.get("completeDefinition"):
            sdef = _parse_struct(node)
            if sdef is not None:
                structs.append(sdef)

        if node.get("kind") == "FunctionDecl" and not node.get("isImplicit"):
            # Skip functions without a body (forward declarations)
            has_body = any(
                child.get("kind") == "CompoundStmt"
                for child in node.get("inner", [])
            )
            if has_body:
                func = _parse_function(node)
                functions.append(func)
                log.info("Parsed function: %s(%s) -> %s",
                         func.name,
                         ", ".join(f"{p.name}: {p.c_type.name}" for p in func.params),
                         func.return_type.name)

    return TranslationUnit(functions=functions, structs=structs)


def _parse_struct(node: dict) -> Optional[StructDef]:
    """Parse a RecordDecl node into a StructDef.

    Returns None for anonymous structs or incomplete definitions.
    """
    name = node.get("name")
    if not name:
        log.debug("Skipping anonymous struct")
        return None

    tag = node.get("tagUsed", "struct")
    if tag != "struct":
        raise StrictCViolation(f"Only struct is supported, got '{tag}'")

    fields = []
    for child in node.get("inner", []):
        if child.get("kind") == "FieldDecl":
            fname = child.get("name", "")
            ftype = parse_clang_type(child["type"])
            fields.append(StructField(name=fname, c_type=ftype))

    sdef = StructDef(name=name, fields=fields)

    # Assign a unique type tag id (starting from 200 to avoid collisions with scalars)
    sdef.type_tag_id = 200 + len(get_struct_defs())

    # Compute layout (offsets, total size, alignment)
    compute_struct_layout(sdef)
    register_struct(sdef)

    log.info("Parsed struct %s: %d fields, size=%d, align=%d",
             name, len(fields), sdef.total_size, sdef.alignment)
    for f in fields:
        log.info("  field %s: type=%s, offset=%d, size=%d, align=%d",
                 f.name, f.c_type.name, f.offset, f.size, f.align)

    return sdef


def _parse_function(node: dict) -> FuncInfo:
    """Parse a FunctionDecl node."""
    name = node["name"]
    ret_type = return_type_from_qual(node["type"]["qualType"])

    params = []
    body_node = None
    for child in node.get("inner", []):
        if child["kind"] == "ParmVarDecl":
            ptype = parse_clang_type(child["type"])
            params.append(VarInfo(name=child["name"], c_type=ptype))
        elif child["kind"] == "CompoundStmt":
            body_node = child

    assert body_node is not None, f"Function {name} has no body"

    # Collect all local variables (includes params in our model)
    locals_list: list[VarInfo] = []
    _collect_locals(body_node, locals_list)

    body = _parse_stmt(body_node)

    return FuncInfo(
        name=name,
        return_type=ret_type,
        params=params,
        locals=locals_list,
        body=body,
    )


def _collect_locals(node: dict, out: list[VarInfo]):
    """Recursively collect VarDecl nodes from the AST."""
    if node.get("kind") == "VarDecl":
        try:
            vtype = parse_clang_type(node["type"])
            out.append(VarInfo(name=node["name"], c_type=vtype))
        except UnsupportedTypeError:
            raise
    for child in node.get("inner", []):
        if isinstance(child, dict):
            _collect_locals(child, out)


def _parse_stmt(node: dict) -> Stmt:
    """Parse a statement node."""
    kind = node.get("kind", "")

    if kind == "CompoundStmt":
        stmts = []
        for child in node.get("inner", []):
            stmts.append(_parse_stmt(child))
        return Stmt(kind="compound", stmts=stmts)

    elif kind == "ReturnStmt":
        inner = node.get("inner", [])
        expr = _parse_expr(inner[0]) if inner else None
        return Stmt(kind="return", expr=expr)

    elif kind == "IfStmt":
        inner = node.get("inner", [])
        # First child is condition, second is then, optional third is else
        cond = _parse_expr(inner[0])
        then_body = _parse_stmt(inner[1])
        else_body = _parse_stmt(inner[2]) if len(inner) > 2 else None
        return Stmt(kind="if", condition=cond, then_body=then_body, else_body=else_body)

    elif kind == "WhileStmt":
        inner = node.get("inner", [])
        cond = _parse_expr(inner[0])
        body = _parse_stmt(inner[1])
        return Stmt(kind="while", condition=cond, loop_body=body)

    elif kind == "DeclStmt":
        # Variable declaration with optional initializer
        inner = node.get("inner", [])
        if inner and inner[0].get("kind") == "VarDecl":
            var_node = inner[0]
            var_name = var_node["name"]
            var_inner = var_node.get("inner", [])
            init_expr = None
            if var_inner:
                init_expr = _parse_expr(var_inner[0])
            return Stmt(kind="decl_init", target_var=var_name, expr=init_expr)
        return Stmt(kind="compound", stmts=[])  # Empty decl

    elif kind == "BinaryOperator" and node.get("opcode") == "=":
        # Assignment: lhs = rhs
        inner = node.get("inner", [])
        lhs = inner[0]
        rhs = inner[1]

        # Check if LHS is a pointer dereference (*p = value)
        deref_target = _extract_deref_target(lhs)
        if deref_target is not None:
            value = _parse_expr(rhs)
            return Stmt(kind="deref_write", target_expr=deref_target, value=value)

        # Check if LHS is a member access (s.field = val or p->field = val)
        member_info = _extract_member_lvalue(lhs)
        if member_info is not None:
            base_expr, field_name, is_arrow = member_info
            value = _parse_expr(rhs)
            return Stmt(
                kind="member_write",
                member_base_expr=base_expr,
                member_name=field_name,
                member_is_arrow=is_arrow,
                value=value,
            )

        target = _extract_var_name(lhs)
        if target is None:
            raise StrictCViolation(
                f"Assignment to non-variable expression not supported: {lhs.get('kind')}"
            )
        value = _parse_expr(rhs)
        return Stmt(kind="assign", target_var=target, value=value)

    elif kind == "GotoStmt":
        raise StrictCViolation("goto is not supported (StrictC restriction)")

    elif kind == "UnaryOperator" and node.get("opcode") in ("++", "--"):
        # Standalone increment/decrement as statement
        inner = node.get("inner", [])
        target = _extract_var_name(inner[0])
        if target is None:
            raise StrictCViolation("Increment/decrement of non-variable not supported")
        # Desugar: x++ becomes x = x + 1
        var_expr = Expr(kind="var_ref", var_name=target)
        one = Expr(kind="int_literal", int_value=1)
        op = "+" if node["opcode"] == "++" else "-"
        rhs = Expr(kind="binop", op=op, lhs=var_expr, rhs=one)
        return Stmt(kind="assign", target_var=target, value=rhs)

    elif kind in ("ForStmt", "DoStmt"):
        raise StrictCViolation(
            f"{kind} not yet supported. Use while loops. "
            f"(for-loop desugaring will be added later)"
        )

    elif kind == "SwitchStmt":
        raise StrictCViolation("switch is not supported (StrictC restriction: no fall-through)")

    elif kind == "BreakStmt":
        return Stmt(kind="break")

    elif kind == "ContinueStmt":
        return Stmt(kind="continue")

    else:
        # Try to parse as an expression statement
        try:
            expr = _parse_expr(node)
            # Check if it's an assignment disguised as an expression
            if expr.kind == "assign_expr":
                return Stmt(kind="assign", target_var=expr.var_name, value=expr.rhs)
            return Stmt(kind="expr", expr=expr)
        except (KeyError, StrictCViolation) as e:
            raise StrictCViolation(
                f"Unsupported statement kind: {kind}. Error: {e}"
            )


def _parse_expr(node: dict) -> Expr:
    """Parse an expression node."""
    kind = node.get("kind", "")

    # Skip implicit casts -- look through to the real expression
    if kind == "ImplicitCastExpr":
        inner = node.get("inner", [])
        if inner:
            return _parse_expr(inner[0])
        raise StrictCViolation(f"ImplicitCastExpr with no inner node")

    # Explicit casts -- also look through for now (Phase 1: same-width integers)
    if kind == "CStyleCastExpr":
        inner = node.get("inner", [])
        if inner:
            return _parse_expr(inner[-1])  # Last child is the operand
        raise StrictCViolation(f"CStyleCastExpr with no inner node")

    if kind == "ParenExpr":
        inner = node.get("inner", [])
        if inner:
            return _parse_expr(inner[0])
        raise StrictCViolation(f"ParenExpr with no inner node")

    if kind == "DeclRefExpr":
        ref = node.get("referencedDecl", {})
        return Expr(kind="var_ref", var_name=ref.get("name", ""))

    if kind == "IntegerLiteral":
        return Expr(kind="int_literal", int_value=int(node.get("value", "0")))

    if kind == "MemberExpr":
        # Struct field access: s.field or p->field
        inner = node.get("inner", [])
        name = node.get("name", "")
        is_arrow = node.get("isArrow", False)
        base = _parse_expr(inner[0]) if inner else None
        return Expr(
            kind="member_access",
            member_name=name,
            member_is_arrow=is_arrow,
            member_base=base,
        )

    if kind == "BinaryOperator":
        opcode = node["opcode"]
        inner = node.get("inner", [])

        # Handle assignment as expression (e.g. in for-loop init)
        if opcode == "=":
            lhs = inner[0]
            rhs = inner[1]
            target = _extract_var_name(lhs)
            if target is None:
                raise StrictCViolation(
                    f"Assignment to non-variable in expression: {lhs.get('kind')}"
                )
            return Expr(kind="assign_expr", var_name=target, rhs=_parse_expr(rhs))

        lhs_expr = _parse_expr(inner[0])
        rhs_expr = _parse_expr(inner[1])

        supported_ops = {
            "+", "-", "*", "/", "%",
            "<", ">", "<=", ">=", "==", "!=",
            "&", "|", "^", "<<", ">>",
            "&&", "||",
        }
        if opcode not in supported_ops:
            raise StrictCViolation(f"Unsupported binary operator: {opcode}")

        return Expr(kind="binop", op=opcode, lhs=lhs_expr, rhs=rhs_expr)

    if kind == "UnaryOperator":
        opcode = node["opcode"]
        inner = node.get("inner", [])

        if opcode in ("++", "--"):
            raise StrictCViolation(
                f"Pre/post increment/decrement in expressions not supported (StrictC). "
                f"Use as standalone statement only."
            )

        if opcode == "*":
            # Pointer dereference: *p (read)
            return Expr(kind="deref", operand=_parse_expr(inner[0]))

        if opcode == "!":
            return Expr(kind="unop", op="!", operand=_parse_expr(inner[0]))
        if opcode == "~":
            return Expr(kind="unop", op="~", operand=_parse_expr(inner[0]))
        if opcode == "-":
            return Expr(kind="unop", op="-", operand=_parse_expr(inner[0]))
        if opcode == "&":
            raise StrictCViolation(
                "Address-of operator (&) on locals not supported (StrictC restriction)"
            )

        raise StrictCViolation(f"Unsupported unary operator: {opcode}")

    if kind == "ConditionalOperator":
        inner = node.get("inner", [])
        cond = _parse_expr(inner[0])
        true_expr = _parse_expr(inner[1])
        false_expr = _parse_expr(inner[2])
        return Expr(kind="ternary", lhs=cond, rhs=true_expr, third=false_expr)

    if kind == "CallExpr":
        raise StrictCViolation(
            "Function calls in expressions not yet supported in Phase 1. "
            "Use standalone call statements."
        )

    raise StrictCViolation(f"Unsupported expression kind: {kind}")


def _extract_member_lvalue(node: dict) -> Optional[tuple[Expr, str, bool]]:
    """Check if an lvalue is a member access (s.field or p->field).

    Returns (base_expr, field_name, is_arrow) or None.
    """
    kind = node.get("kind", "")
    if kind == "MemberExpr":
        inner = node.get("inner", [])
        name = node.get("name", "")
        is_arrow = node.get("isArrow", False)
        base = _parse_expr(inner[0]) if inner else None
        return (base, name, is_arrow)
    if kind == "ImplicitCastExpr":
        inner = node.get("inner", [])
        if inner:
            return _extract_member_lvalue(inner[0])
    if kind == "ParenExpr":
        inner = node.get("inner", [])
        if inner:
            return _extract_member_lvalue(inner[0])
    return None


def _extract_deref_target(node: dict) -> Optional[Expr]:
    """Check if an lvalue expression is a pointer dereference (*p).

    Returns the pointer expression if it is a dereference, None otherwise.
    """
    kind = node.get("kind", "")
    if kind == "UnaryOperator" and node.get("opcode") == "*":
        inner = node.get("inner", [])
        if inner:
            return _parse_expr(inner[0])
    if kind == "ImplicitCastExpr":
        inner = node.get("inner", [])
        if inner:
            return _extract_deref_target(inner[0])
    if kind == "ParenExpr":
        inner = node.get("inner", [])
        if inner:
            return _extract_deref_target(inner[0])
    return None


def _extract_var_name(node: dict) -> Optional[str]:
    """Extract variable name from an lvalue expression node."""
    kind = node.get("kind", "")
    if kind == "DeclRefExpr":
        return node.get("referencedDecl", {}).get("name")
    if kind == "ImplicitCastExpr":
        inner = node.get("inner", [])
        if inner:
            return _extract_var_name(inner[0])
    if kind == "ParenExpr":
        inner = node.get("inner", [])
        if inner:
            return _extract_var_name(inner[0])
    return None


def load_ast(path: str) -> dict:
    """Load clang JSON AST from a file.

    Args:
        path: Path to the JSON file.

    Returns:
        The parsed JSON dict.
    """
    with open(path, 'r') as f:
        return json.load(f)
