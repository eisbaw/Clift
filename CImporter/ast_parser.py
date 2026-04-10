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
    kind: str  # "var_ref", "int_literal", "binop", "unop", "ternary", "deref",
               # "member_access", "call_expr", "cast_expr", "sizeof_expr"
    # Fields depend on kind:
    var_name: Optional[str] = None       # for var_ref, call_expr (callee name)
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
    # For call_expr:
    call_args: list['Expr'] = field(default_factory=list)  # function arguments
    # For cast_expr:
    cast_from: Optional[CType] = None  # source type of cast
    cast_to: Optional[CType] = None    # target type of cast
    # For sizeof_expr:
    sizeof_type: Optional[CType] = None  # type whose size is being taken

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
class EnumConstant:
    """An enumerator within an enum definition."""
    name: str
    value: int

@dataclass
class EnumInfo:
    """An enum definition."""
    name: str  # May be empty for anonymous enums
    constants: list[EnumConstant]

@dataclass
class GlobalVarInfo:
    """A file-scope global variable."""
    name: str
    c_type: CType
    init_value: Optional[int]  # Integer initializer, or None if no init

@dataclass
class TranslationUnit:
    """Parsed translation unit (one .c file)."""
    functions: list[FuncInfo]
    structs: list[StructDef]  # Struct definitions in order
    enums: list[EnumInfo] = field(default_factory=list)
    globals: list[GlobalVarInfo] = field(default_factory=list)
    # Lookup tables populated during parsing
    enum_constants: dict[str, int] = field(default_factory=dict)  # name -> value
    global_var_names: set[str] = field(default_factory=set)  # names of globals


# --- Parser context (module-level, set during parse_translation_unit) ---
# These allow _parse_expr to distinguish globals/enums without threading
# context through every recursive call.
_ENUM_CONSTANTS: dict[str, int] = {}
_GLOBAL_VAR_NAMES: set[str] = set()


def parse_translation_unit(ast: dict) -> TranslationUnit:
    """Parse a clang JSON AST root node into a TranslationUnit.

    Args:
        ast: The root dict from clang's -ast-dump=json output.

    Returns:
        TranslationUnit with all user-defined functions, structs, enums,
        typedefs (resolved), and global variables.
    """
    assert ast.get("kind") == "TranslationUnitDecl", \
        f"Expected TranslationUnitDecl, got {ast.get('kind')}"

    global _ENUM_CONSTANTS, _GLOBAL_VAR_NAMES
    clear_struct_defs()
    _ENUM_CONSTANTS = {}
    _GLOBAL_VAR_NAMES = set()
    structs = []
    functions = []
    enums = []
    globals_list = []
    enum_constants: dict[str, int] = {}
    global_var_names: set[str] = set()

    for node in ast.get("inner", []):
        kind = node.get("kind", "")

        # Parse enum definitions
        if kind == "EnumDecl":
            enum_info = _parse_enum(node)
            if enum_info is not None:
                enums.append(enum_info)
                for ec in enum_info.constants:
                    enum_constants[ec.name] = ec.value
                    _ENUM_CONSTANTS[ec.name] = ec.value

        # Parse typedefs: resolve to underlying type and register in type map.
        # This is transparent — we don't emit anything for typedefs, but we
        # make sure their names are recognized when used as types.
        if kind == "TypedefDecl":
            _register_typedef(node)

        # Parse struct definitions (must come before functions that use them)
        if kind == "RecordDecl" and node.get("completeDefinition"):
            sdef = _parse_struct(node)
            if sdef is not None:
                structs.append(sdef)

        # Parse file-scope global variables
        if kind == "VarDecl" and not node.get("isImplicit"):
            gvar = _parse_global_var(node, enum_constants)
            if gvar is not None:
                globals_list.append(gvar)
                global_var_names.add(gvar.name)
                _GLOBAL_VAR_NAMES.add(gvar.name)

        if kind == "FunctionDecl" and not node.get("isImplicit"):
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

    return TranslationUnit(
        functions=functions, structs=structs, enums=enums,
        globals=globals_list, enum_constants=enum_constants,
        global_var_names=global_var_names,
    )


def _parse_enum(node: dict) -> Optional[EnumInfo]:
    """Parse an EnumDecl node into an EnumInfo.

    Returns None for system/implicit enums (no name and not in user source).
    """
    name = node.get("name", "")

    constants = []
    for child in node.get("inner", []):
        if child.get("kind") == "EnumConstantDecl":
            ec_name = child.get("name", "")
            # Value is in the first ConstantExpr inner node
            ec_value = 0
            inner = child.get("inner", [])
            if inner and "value" in inner[0]:
                ec_value = int(inner[0]["value"])
            constants.append(EnumConstant(name=ec_name, value=ec_value))

    if not constants:
        return None

    log.info("Parsed enum %s: %d constants", name or "(anonymous)", len(constants))
    for ec in constants:
        log.info("  %s = %d", ec.name, ec.value)

    return EnumInfo(name=name, constants=constants)


def _register_typedef(node: dict):
    """Register a TypedefDecl in the type map.

    Typedefs are resolved transparently: we add the typedef name to the
    clang type map pointing to the underlying type. This means when the
    typedef name appears as a qualType, parse_clang_type will resolve it.

    Only registers typedefs whose underlying type we already support.
    System typedefs (stdint.h etc.) are already handled by the existing map.
    """
    name = node.get("name", "")
    if not name:
        return

    type_node = node.get("type", {})
    desugared = type_node.get("desugaredQualType", "")
    qual = type_node.get("qualType", "")

    # Skip if already in the type map (system typedefs like uint32_t)
    from .c_types import _CLANG_TYPE_MAP
    if name in _CLANG_TYPE_MAP:
        return

    # Try to resolve the underlying type
    try:
        # Prefer desugared form
        if desugared and desugared in _CLANG_TYPE_MAP:
            _CLANG_TYPE_MAP[name] = _CLANG_TYPE_MAP[desugared]
            log.info("Registered typedef: %s -> %s", name, desugared)
            return
        if qual and qual in _CLANG_TYPE_MAP:
            _CLANG_TYPE_MAP[name] = _CLANG_TYPE_MAP[qual]
            log.info("Registered typedef: %s -> %s", name, qual)
            return
        # Try full parse of the type (handles pointers, structs)
        underlying = parse_clang_type(type_node)
        _CLANG_TYPE_MAP[name] = underlying
        log.info("Registered typedef: %s -> %s", name, underlying.name)
    except (UnsupportedTypeError, KeyError):
        log.debug("Skipping unsupported typedef: %s (qualType=%s)", name, qual)


def _parse_global_var(node: dict, enum_constants: dict[str, int]) -> Optional[GlobalVarInfo]:
    """Parse a file-scope VarDecl into a GlobalVarInfo.

    Returns None if:
    - The variable is a local (has no file-level loc -- though file-scope
      VarDecl is already filtered by the caller)
    - The type is unsupported
    - It's a system-provided variable
    """
    name = node.get("name", "")
    if not name:
        return None

    # Skip extern declarations (no storage)
    if node.get("storageClass") == "extern":
        return None

    try:
        c_type = parse_clang_type(node["type"])
    except (UnsupportedTypeError, KeyError):
        log.debug("Skipping global with unsupported type: %s", name)
        return None

    # Extract integer initializer value
    init_value = None
    if node.get("init") is not None:
        init_value = _extract_init_value(node, enum_constants)

    log.info("Parsed global variable: %s : %s = %s", name, c_type.name,
             init_value if init_value is not None else "default")
    return GlobalVarInfo(name=name, c_type=c_type, init_value=init_value)


def _extract_init_value(node: dict, enum_constants: dict[str, int]) -> Optional[int]:
    """Extract a constant integer initializer from a VarDecl node.

    Handles:
    - Integer literals (direct value)
    - Enum constant references (looked up in enum_constants)
    - ConstantExpr wrappers

    Returns None if the initializer is not a simple integer constant.
    """
    inner = node.get("inner", [])
    for child in inner:
        val = _extract_const_int(child, enum_constants)
        if val is not None:
            return val
    return None


def _extract_const_int(node: dict, enum_constants: dict[str, int]) -> Optional[int]:
    """Recursively extract a constant integer from an AST expression node."""
    kind = node.get("kind", "")

    if kind == "IntegerLiteral":
        return int(node.get("value", "0"))

    if kind == "ConstantExpr" and "value" in node:
        return int(node["value"])

    if kind == "DeclRefExpr":
        ref = node.get("referencedDecl", {})
        if ref.get("kind") == "EnumConstantDecl":
            name = ref.get("name", "")
            if name in enum_constants:
                return enum_constants[name]

    # Look through implicit casts and constant expressions
    if kind in ("ImplicitCastExpr", "ConstantExpr", "ParenExpr"):
        for child in node.get("inner", []):
            val = _extract_const_int(child, enum_constants)
            if val is not None:
                return val

    return None


def _parse_struct(node: dict) -> Optional[StructDef]:
    """Parse a RecordDecl node into a StructDef (handles both struct and union).

    Returns None for anonymous records or incomplete definitions.
    """
    name = node.get("name")
    if not name:
        log.debug("Skipping anonymous struct/union")
        return None

    tag = node.get("tagUsed", "struct")
    if tag not in ("struct", "union"):
        raise StrictCViolation(f"Only struct and union are supported, got '{tag}'")

    is_union = (tag == "union")

    fields = []
    for child in node.get("inner", []):
        if child.get("kind") == "FieldDecl":
            fname = child.get("name", "")
            ftype = parse_clang_type(child["type"])
            fields.append(StructField(name=fname, c_type=ftype))

    sdef = StructDef(name=name, fields=fields, is_union=is_union)

    # Assign a unique type tag id (starting from 200 to avoid collisions with scalars)
    sdef.type_tag_id = 200 + len(get_struct_defs())

    # Compute layout (offsets, total size, alignment)
    compute_struct_layout(sdef)
    register_struct(sdef)

    kind_str = "union" if is_union else "struct"
    log.info("Parsed %s %s: %d fields, size=%d, align=%d",
             kind_str, name, len(fields), sdef.total_size, sdef.alignment)
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

        # Check if LHS is an array subscript (arr[i] = value)
        array_sub = _extract_array_subscript_lvalue(lhs)
        if array_sub is not None:
            base_expr, index_expr = array_sub
            value = _parse_expr(rhs)
            # Emit as deref_write with the computed pointer
            # arr[i] = val => *(arr + i*sizeof(elem)) = val
            return Stmt(
                kind="array_write",
                member_base_expr=base_expr,  # reuse field: base pointer
                target_expr=index_expr,       # reuse field: index expression
                value=value,
            )

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
        # Distinguish global variable assignments from local assignments
        if target in _GLOBAL_VAR_NAMES:
            return Stmt(kind="global_assign", target_var=target, value=value)
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

    elif kind == "ForStmt":
        # Desugar: for (init; cond; step) body -> init; while (cond) { body; step }
        inner = node.get("inner", [])
        # ForStmt children: [0]=init, [1]=condvar (empty dict if none), [2]=cond, [3]=step, [4]=body
        # Some children may be missing (empty dict {}) if omitted in source.
        if len(inner) < 5:
            raise StrictCViolation(
                f"ForStmt has {len(inner)} children, expected 5 "
                "(init, condvar, cond, step, body)"
            )
        init_node = inner[0]
        cond_node = inner[2]
        step_node = inner[3]
        body_node = inner[4]

        # Parse init (may be DeclStmt or expression)
        init_stmt = _parse_stmt(init_node) if init_node.get("kind") else Stmt(kind="compound", stmts=[])

        # Parse condition
        cond_expr = _parse_expr(cond_node) if cond_node.get("kind") else None
        if cond_expr is None:
            raise StrictCViolation("for-loop without condition not supported (StrictC)")

        # Parse step (increment expression)
        step_stmt = _parse_stmt(step_node) if step_node.get("kind") else Stmt(kind="compound", stmts=[])

        # Parse body
        body_stmt = _parse_stmt(body_node)

        # Desugar: compound(init, while(cond, compound(body, step)))
        while_body = Stmt(kind="compound", stmts=[body_stmt, step_stmt])
        while_stmt = Stmt(kind="while", condition=cond_expr, loop_body=while_body)
        return Stmt(kind="compound", stmts=[init_stmt, while_stmt])

    elif kind == "DoStmt":
        # Desugar: do { body } while (cond) -> body; while (cond) { body }
        inner = node.get("inner", [])
        if len(inner) < 2:
            raise StrictCViolation(f"DoStmt has {len(inner)} children, expected 2 (body, cond)")
        body_stmt = _parse_stmt(inner[0])
        cond_expr = _parse_expr(inner[1])
        # Deep-copy body for the while loop body (since AST is immutable dataclasses, sharing is fine)
        while_stmt = Stmt(kind="while", condition=cond_expr, loop_body=body_stmt)
        return Stmt(kind="compound", stmts=[body_stmt, while_stmt])

    elif kind == "SwitchStmt":
        # Desugar: switch(x) { case v1: ...; case v2: ...; default: ... }
        #       -> nested if/else: if (x == v1) ... else if (x == v2) ... else ...
        # StrictC: no fall-through, each case must end with break.
        inner = node.get("inner", [])
        if len(inner) < 2:
            raise StrictCViolation(f"SwitchStmt has {len(inner)} children, expected >= 2")
        switch_expr = _parse_expr(inner[0])
        compound = inner[1]
        if compound.get("kind") != "CompoundStmt":
            raise StrictCViolation(f"SwitchStmt body is not CompoundStmt: {compound.get('kind')}")

        cases, default_body = _parse_switch_cases(compound, switch_expr)
        return _build_switch_if_chain(cases, default_body)

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


def _try_extract_result_type(node: dict) -> Optional[CType]:
    """Try to extract the result CType from a clang AST node's type field.

    Returns None if the type is not recognized or not present.
    Does not raise on failure -- callers use this for best-effort type tracking.
    """
    type_node = node.get("type")
    if not type_node:
        return None
    try:
        return parse_clang_type(type_node)
    except (UnsupportedTypeError, KeyError):
        return None


def _parse_expr(node: dict) -> Expr:
    """Parse an expression node."""
    kind = node.get("kind", "")

    # Skip implicit casts -- look through to the real expression
    if kind == "ImplicitCastExpr":
        inner = node.get("inner", [])
        if inner:
            return _parse_expr(inner[0])
        raise StrictCViolation(f"ImplicitCastExpr with no inner node")

    # Explicit casts: extract source and target types, emit conversion
    if kind == "CStyleCastExpr":
        inner = node.get("inner", [])
        if not inner:
            raise StrictCViolation(f"CStyleCastExpr with no inner node")
        cast_kind = node.get("castKind", "")
        # NoOp casts (same type): pass through
        if cast_kind == "NoOp":
            return _parse_expr(inner[-1])
        # Pointer casts
        if cast_kind == "NullToPointer":
            return _parse_expr(inner[-1])
        if cast_kind in ("PointerToBoolean", "PointerToIntegral"):
            return _parse_expr(inner[-1])
        if cast_kind == "IntegralToPointer":
            return _parse_expr(inner[-1])
        if cast_kind == "BitCast":
            # Pointer-to-pointer cast (e.g., void* -> uint32_t*).
            # Both types are pointers with the same representation.
            # Emit a ptr_cast_expr so the emitter can insert a type coercion.
            target_type = _try_extract_result_type(node)
            operand = _parse_expr(inner[-1])
            if target_type is not None and target_type.is_pointer:
                return Expr(kind="ptr_cast_expr", operand=operand,
                           cast_from=operand.result_type, cast_to=target_type,
                           result_type=target_type)
            return operand
        # IntegralCast: widening/narrowing between integer types
        target_type = _try_extract_result_type(node)
        operand = _parse_expr(inner[-1])
        source_type = operand.result_type
        # If we can determine both types, emit a cast_expr
        if target_type is not None and source_type is not None:
            # Same width or unknown: pass through (identity cast)
            if target_type.bits == source_type.bits and target_type.signed == source_type.signed:
                return Expr(kind=operand.kind, var_name=operand.var_name,
                           int_value=operand.int_value, op=operand.op,
                           lhs=operand.lhs, rhs=operand.rhs, third=operand.third,
                           operand=operand.operand, result_type=target_type,
                           member_name=operand.member_name,
                           member_is_arrow=operand.member_is_arrow,
                           member_base=operand.member_base,
                           call_args=operand.call_args)
            return Expr(kind="cast_expr", operand=operand,
                       cast_from=source_type, cast_to=target_type,
                       result_type=target_type)
        # Fallback: pass through with target type
        if target_type is not None:
            operand.result_type = target_type
        return operand

    if kind == "ParenExpr":
        inner = node.get("inner", [])
        if inner:
            return _parse_expr(inner[0])
        raise StrictCViolation(f"ParenExpr with no inner node")

    if kind == "DeclRefExpr":
        ref = node.get("referencedDecl", {})
        ref_name = ref.get("name", "")
        ref_kind = ref.get("kind", "")
        result_type = _try_extract_result_type(node)

        # Enum constant reference -> integer literal
        if ref_kind == "EnumConstantDecl" and ref_name in _ENUM_CONSTANTS:
            return Expr(kind="int_literal", int_value=_ENUM_CONSTANTS[ref_name])

        # Global variable reference -> global_ref (accessed via s.globals.field)
        if ref_name in _GLOBAL_VAR_NAMES:
            return Expr(kind="global_ref", var_name=ref_name, result_type=result_type)

        return Expr(kind="var_ref", var_name=ref_name, result_type=result_type)

    if kind == "IntegerLiteral":
        return Expr(kind="int_literal", int_value=int(node.get("value", "0")))

    if kind == "CharacterLiteral":
        # Character literal: 'a' -> its integer value
        return Expr(kind="int_literal", int_value=int(node.get("value", 0)),
                    result_type=_try_extract_result_type(node))

    if kind == "ConstantExpr":
        # ConstantExpr is a wrapper around a compile-time constant.
        # It may have a 'value' field directly, or we look through to inner.
        if "value" in node:
            return Expr(kind="int_literal", int_value=int(node["value"]))
        inner = node.get("inner", [])
        if inner:
            return _parse_expr(inner[0])
        raise StrictCViolation("ConstantExpr with no value and no inner node")

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

        result_type = _try_extract_result_type(node)
        return Expr(kind="binop", op=opcode, lhs=lhs_expr, rhs=rhs_expr, result_type=result_type)

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

    if kind == "ArraySubscriptExpr":
        # Array element access: base[index]
        # First child is the base (pointer/array), second is the index
        inner = node.get("inner", [])
        if len(inner) < 2:
            raise StrictCViolation("ArraySubscriptExpr with fewer than 2 children")
        base = _parse_expr(inner[0])
        index = _parse_expr(inner[1])
        result_type = _try_extract_result_type(node)
        return Expr(kind="array_subscript", lhs=base, rhs=index, result_type=result_type)

    if kind == "CallExpr":
        # Parse function call: first inner is function reference, rest are args
        inner = node.get("inner", [])
        if not inner:
            raise StrictCViolation("CallExpr with no inner nodes")
        # First child is the callee (function reference, possibly via ImplicitCastExpr)
        callee_name = _extract_callee_name(inner[0])
        if callee_name is None:
            raise StrictCViolation(
                "Only direct function calls are supported (no function pointers). "
                f"Callee node kind: {inner[0].get('kind')}"
            )
        # Remaining children are arguments
        args = [_parse_expr(arg) for arg in inner[1:]]
        result_type = _try_extract_result_type(node)
        return Expr(kind="call_expr", var_name=callee_name,
                    result_type=result_type, call_args=args)

    if kind == "UnaryExprOrTypeTraitExpr":
        # sizeof(type) or sizeof(expr)
        name = node.get("name", "")
        if name == "sizeof":
            # sizeof(type): has argType field
            arg_type_node = node.get("argType")
            if arg_type_node:
                try:
                    sizeof_ctype = parse_clang_type(arg_type_node)
                    return Expr(kind="sizeof_expr", sizeof_type=sizeof_ctype,
                               result_type=_try_extract_result_type(node))
                except UnsupportedTypeError:
                    pass
            # sizeof(expr): determine type from inner expression
            inner = node.get("inner", [])
            if inner:
                operand = _parse_expr(inner[0])
                if operand.result_type:
                    return Expr(kind="sizeof_expr", sizeof_type=operand.result_type,
                                result_type=_try_extract_result_type(node))
            raise StrictCViolation(
                f"sizeof with unresolvable type: {node.get('argType', {})}"
            )
        raise StrictCViolation(f"Unsupported UnaryExprOrTypeTraitExpr: {name}")

    raise StrictCViolation(f"Unsupported expression kind: {kind}")


def _parse_switch_cases(compound: dict, switch_expr: Expr) -> tuple[list[tuple[Expr, Stmt]], Optional[Stmt]]:
    """Parse the body of a SwitchStmt into a list of (condition, body) pairs.

    Returns:
        (cases, default_body) where cases is [(condition_expr, body_stmt), ...].
        The condition is an equality check: switch_expr == case_value.
        default_body is the body for the default case, or None.
    """
    children = compound.get("inner", [])
    cases = []
    default_body = None
    i = 0
    while i < len(children):
        child = children[i]
        ckind = child.get("kind", "")

        if ckind == "CaseStmt":
            case_inner = child.get("inner", [])
            if len(case_inner) < 2:
                raise StrictCViolation(f"CaseStmt has {len(case_inner)} children, expected >= 2")
            # First child is the case value, rest are body statements
            case_value = _parse_expr(case_inner[0])
            body_stmts = [_parse_stmt(c) for c in case_inner[1:]]
            # Collect subsequent statements until BreakStmt or next CaseStmt/DefaultStmt
            i += 1
            while i < len(children):
                next_kind = children[i].get("kind", "")
                if next_kind in ("CaseStmt", "DefaultStmt"):
                    break
                if next_kind == "BreakStmt":
                    i += 1  # Skip the break
                    break
                body_stmts.append(_parse_stmt(children[i]))
                i += 1
            # Build condition: switch_expr == case_value
            cond = Expr(kind="binop", op="==", lhs=switch_expr, rhs=case_value)
            body = Stmt(kind="compound", stmts=body_stmts) if len(body_stmts) > 1 else (
                body_stmts[0] if body_stmts else Stmt(kind="compound", stmts=[])
            )
            cases.append((cond, body))

        elif ckind == "DefaultStmt":
            case_inner = child.get("inner", [])
            body_stmts = [_parse_stmt(c) for c in case_inner]
            # Collect subsequent statements until BreakStmt
            i += 1
            while i < len(children):
                next_kind = children[i].get("kind", "")
                if next_kind in ("CaseStmt", "DefaultStmt"):
                    break
                if next_kind == "BreakStmt":
                    i += 1
                    break
                body_stmts.append(_parse_stmt(children[i]))
                i += 1
            default_body = Stmt(kind="compound", stmts=body_stmts) if len(body_stmts) > 1 else (
                body_stmts[0] if body_stmts else Stmt(kind="compound", stmts=[])
            )

        else:
            # Skip stray nodes (shouldn't happen in well-formed switch)
            i += 1

    return cases, default_body


def _build_switch_if_chain(cases: list[tuple[Expr, Stmt]], default_body: Optional[Stmt]) -> Stmt:
    """Build a nested if/else chain from switch cases.

    The last else branch is the default case (or skip if no default).
    """
    if not cases:
        return default_body if default_body else Stmt(kind="compound", stmts=[])

    # Build from the end: last case gets default as else
    result = default_body if default_body else Stmt(kind="compound", stmts=[])
    for cond, body in reversed(cases):
        result = Stmt(kind="if", condition=cond, then_body=body, else_body=result)
    return result


def _extract_array_subscript_lvalue(node: dict) -> Optional[tuple[Expr, Expr]]:
    """Check if an lvalue is an array subscript (arr[i]).

    Returns (base_expr, index_expr) or None.
    """
    kind = node.get("kind", "")
    if kind == "ArraySubscriptExpr":
        inner = node.get("inner", [])
        if len(inner) >= 2:
            base = _parse_expr(inner[0])
            index = _parse_expr(inner[1])
            return (base, index)
    if kind == "ImplicitCastExpr":
        inner = node.get("inner", [])
        if inner:
            return _extract_array_subscript_lvalue(inner[0])
    return None


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


def _extract_callee_name(node: dict) -> Optional[str]:
    """Extract the function name from a callee expression in a CallExpr.

    The callee is typically an ImplicitCastExpr wrapping a DeclRefExpr
    that references a FunctionDecl.
    """
    kind = node.get("kind", "")
    if kind == "DeclRefExpr":
        ref = node.get("referencedDecl", {})
        if ref.get("kind") == "FunctionDecl":
            return ref.get("name")
    if kind == "ImplicitCastExpr":
        inner = node.get("inner", [])
        if inner:
            return _extract_callee_name(inner[0])
    if kind == "ParenExpr":
        inner = node.get("inner", [])
        if inner:
            return _extract_callee_name(inner[0])
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
