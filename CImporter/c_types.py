"""C type representation for the CImporter.

Maps clang's type representations to Lean 4 types.
This module is in the TCB -- incorrect type mapping invalidates all downstream proofs.

Supported types (StrictC subset):
  - uint8_t, uint16_t, uint32_t, uint64_t (unsigned integers)
  - int8_t, int16_t, int32_t, int64_t (signed integers)
  - void (return type only)
  - _Bool / bool
  - Pointers to supported types (Phase 3a+3b)
  - Structs (Phase 3b)

Unsupported (rejected with clear error):
  - float, double (no floating point in Phase 1)
  - arrays, VLAs
"""

from dataclasses import dataclass, field
from typing import Optional
import logging
import re

log = logging.getLogger(__name__)


@dataclass(frozen=True)
class CType:
    """A C type as seen by the importer."""
    name: str        # Canonical name: "uint32_t", "int64_t", "void", "bool", "struct node"
    signed: bool     # True for int8_t..int64_t
    bits: int        # Bit width (0 for void, structs, pointers)
    is_pointer: bool = False  # True for pointer types (e.g. uint32_t *)
    pointee: Optional['CType'] = None  # The type being pointed to (for pointers)
    is_struct: bool = False  # True for struct types
    struct_name: Optional[str] = None  # e.g. "node" for struct node

    @property
    def lean_type(self) -> str:
        """Lean 4 type name for this C type."""
        if self.is_pointer:
            pointee_lean = self.pointee.lean_type
            # Wrap compound types in parens for Ptr
            if ' ' in pointee_lean and not pointee_lean.startswith('('):
                return f"Ptr ({pointee_lean})"
            return f"Ptr {pointee_lean}"
        if self.is_struct:
            return f"C_{self.struct_name}"
        if self.name == "void":
            return "Unit"
        if self.name == "bool":
            return "Bool"
        # Phase 3b: map all integer types to unsigned Lean types for memory layout.
        # Signed arithmetic semantics are handled in Phase 2 (WordAbstract).
        # The bit patterns are identical (two's complement), so this is correct
        # for memory operations.
        return f"UInt{self.bits}"

    @property
    def lean_default(self) -> str:
        """Lean 4 default value for this type."""
        if self.is_pointer:
            return "default"
        if self.is_struct:
            return "default"
        if self.name == "void":
            return "()"
        if self.name == "bool":
            return "false"
        return "0"

    @property
    def is_unsigned(self) -> bool:
        return not self.signed and self.name != "void" and self.name != "bool" and not self.is_pointer and not self.is_struct


@dataclass
class StructField:
    """A field in a C struct."""
    name: str
    c_type: CType
    # Computed by layout algorithm:
    offset: int = 0
    size: int = 0
    align: int = 0


@dataclass
class StructDef:
    """A C struct definition with computed layout."""
    name: str           # e.g. "node"
    fields: list[StructField] = field(default_factory=list)
    # Computed by layout algorithm:
    total_size: int = 0
    alignment: int = 1
    type_tag_id: int = 0  # Unique TypeTag id for this struct

    @property
    def lean_name(self) -> str:
        """Lean 4 structure name: C_<name>."""
        return f"C_{self.name}"

    @property
    def c_type(self) -> CType:
        """Get a CType instance for this struct."""
        return CType(
            name=f"struct {self.name}",
            signed=False,
            bits=0,
            is_struct=True,
            struct_name=self.name,
        )


# Canonical type instances
VOID = CType("void", False, 0)
BOOL = CType("bool", False, 1)

UINT8  = CType("uint8_t", False, 8)
UINT16 = CType("uint16_t", False, 16)
UINT32 = CType("uint32_t", False, 32)
UINT64 = CType("uint64_t", False, 64)

INT8  = CType("int8_t", True, 8)
INT16 = CType("int16_t", True, 16)
INT32 = CType("int32_t", True, 32)
INT64 = CType("int64_t", True, 64)


# Mapping from clang's desugaredQualType / qualType strings to our CType.
# Clang desugars typedefs, so we see the underlying type.
_CLANG_TYPE_MAP: dict[str, CType] = {
    # Desugared forms (what clang gives us)
    "unsigned char": UINT8,
    "unsigned short": UINT16,
    "unsigned int": UINT32,
    "unsigned long": UINT64,
    "unsigned long long": UINT64,
    "signed char": INT8,
    "short": INT16,
    "int": INT32,
    "long": INT64,
    "long long": INT64,
    "_Bool": BOOL,
    "void": VOID,
    # Typedef forms (qualType when not desugared)
    "uint8_t": UINT8,
    "uint16_t": UINT16,
    "uint32_t": UINT32,
    "uint64_t": UINT64,
    "int8_t": INT8,
    "int16_t": INT16,
    "int32_t": INT32,
    "int64_t": INT64,
    "bool": BOOL,
}

# Known struct definitions, populated by the parser.
# Maps "struct <name>" -> StructDef
_STRUCT_DEFS: dict[str, StructDef] = {}


def register_struct(sdef: StructDef):
    """Register a parsed struct definition so pointer types can reference it."""
    key = f"struct {sdef.name}"
    _STRUCT_DEFS[key] = sdef
    log.info("Registered struct: %s (size=%d, align=%d)", key, sdef.total_size, sdef.alignment)


def get_struct_defs() -> dict[str, StructDef]:
    """Get all registered struct definitions."""
    return dict(_STRUCT_DEFS)


def clear_struct_defs():
    """Clear registered structs (for testing)."""
    _STRUCT_DEFS.clear()


class UnsupportedTypeError(Exception):
    """Raised when the importer encounters a C type it cannot handle."""
    pass


def parse_clang_type(type_node: dict) -> CType:
    """Parse a clang JSON type node into a CType.

    Args:
        type_node: The 'type' dict from a clang AST node.
                   Has 'qualType' and optionally 'desugaredQualType'.

    Returns:
        The corresponding CType.

    Raises:
        UnsupportedTypeError: If the type is not in the StrictC subset.
    """
    # Prefer desugared form (canonical), fall back to qualType
    desugared = type_node.get("desugaredQualType", "")
    qual = type_node.get("qualType", "")

    # Try desugared first
    if desugared in _CLANG_TYPE_MAP:
        return _CLANG_TYPE_MAP[desugared]

    # Try qualType (handles typedefs that clang didn't desugar)
    if qual in _CLANG_TYPE_MAP:
        return _CLANG_TYPE_MAP[qual]

    # Check for struct types (Phase 3b)
    struct_match = _match_struct_type(qual) or _match_struct_type(desugared)
    if struct_match:
        return struct_match

    # Check for unsupported types and give clear errors
    for bad in ("float", "double", "long double"):
        if bad in desugared or bad in qual:
            raise UnsupportedTypeError(
                f"Floating point type '{qual}' not supported (StrictC restriction). "
                f"Only integer types are allowed in Phase 1."
            )

    # Handle pointer types (Phase 3a+3b: scalar and struct pointers)
    if "*" in qual or "*" in desugared:
        return _parse_pointer_type(type_node)

    raise UnsupportedTypeError(
        f"Unknown C type: qualType='{qual}', desugaredQualType='{desugared}'. "
        f"Supported types: {sorted(_CLANG_TYPE_MAP.keys())} + registered structs"
    )


def _match_struct_type(type_str: str) -> Optional[CType]:
    """Check if a type string is a known struct type.

    Returns CType if it matches, None otherwise.
    """
    if not type_str:
        return None
    # Match "struct <name>" exactly
    m = re.match(r'^struct\s+(\w+)$', type_str)
    if m:
        struct_name = m.group(1)
        key = f"struct {struct_name}"
        if key in _STRUCT_DEFS:
            return _STRUCT_DEFS[key].c_type
        # Struct not yet registered -- create a forward reference CType.
        # This handles self-referential structs (e.g. struct node *next).
        return CType(
            name=key,
            signed=False,
            bits=0,
            is_struct=True,
            struct_name=struct_name,
        )
    return None


def _parse_pointer_type(type_node: dict) -> CType:
    """Parse a pointer type from a clang type node.

    Handles types like 'uint32_t *', 'struct node *' by stripping
    the '*' and recursing to find the pointee type.
    """
    desugared = type_node.get("desugaredQualType", "")
    qual = type_node.get("qualType", "")

    # Strip the pointer: "unsigned int *" -> "unsigned int"
    pointee_str = desugared.rstrip("* ").strip() if desugared else qual.rstrip("* ").strip()

    # Try scalar types first
    if pointee_str in _CLANG_TYPE_MAP:
        pointee = _CLANG_TYPE_MAP[pointee_str]
        return CType(
            name=f"{pointee.name} *",
            signed=False,
            bits=0,
            is_pointer=True,
            pointee=pointee,
        )

    # Try struct types
    struct_pointee = _match_struct_type(pointee_str)
    if struct_pointee:
        return CType(
            name=f"{pointee_str} *",
            signed=False,
            bits=0,
            is_pointer=True,
            pointee=struct_pointee,
        )

    # Try qualType without '*'
    qual_stripped = qual.rstrip("* ").strip()
    if qual_stripped in _CLANG_TYPE_MAP:
        pointee = _CLANG_TYPE_MAP[qual_stripped]
        return CType(
            name=f"{pointee.name} *",
            signed=False,
            bits=0,
            is_pointer=True,
            pointee=pointee,
        )

    # Try qualType as struct
    struct_pointee = _match_struct_type(qual_stripped)
    if struct_pointee:
        return CType(
            name=f"{qual_stripped} *",
            signed=False,
            bits=0,
            is_pointer=True,
            pointee=struct_pointee,
        )

    raise UnsupportedTypeError(
        f"Pointer to unsupported type: '{qual}'. "
        f"Supported pointee types: scalars + registered structs."
    )


def return_type_from_qual(qual_type_str: str) -> CType:
    """Extract return type from a function's qualType string.

    E.g. "uint32_t (uint32_t, uint32_t)" -> UINT32
         "int (struct node *)" -> INT32

    Args:
        qual_type_str: The function's qualType from clang JSON.

    Returns:
        The return CType.
    """
    # Function qualType format: "return_type (param_types)"
    ret_str = qual_type_str.split("(")[0].strip()
    if ret_str in _CLANG_TYPE_MAP:
        return _CLANG_TYPE_MAP[ret_str]
    # Try struct type
    struct_type = _match_struct_type(ret_str)
    if struct_type:
        return struct_type
    raise UnsupportedTypeError(f"Unknown return type: '{ret_str}'")


# x86-64 LP64 ABI: size and alignment for scalar types
_SCALAR_SIZE_ALIGN: dict[str, tuple[int, int]] = {
    "uint8_t": (1, 1),
    "uint16_t": (2, 2),
    "uint32_t": (4, 4),
    "uint64_t": (8, 8),
    "int8_t": (1, 1),
    "int16_t": (2, 2),
    "int32_t": (4, 4),
    "int64_t": (8, 8),
    "bool": (1, 1),
}


def type_size_align(ctype: CType) -> tuple[int, int]:
    """Get (size, alignment) in bytes for a CType on x86-64 LP64.

    This is the single source of truth for ABI layout. Must match gcc.
    """
    if ctype.is_pointer:
        return (8, 8)  # All pointers are 8 bytes on LP64
    if ctype.is_struct:
        key = f"struct {ctype.struct_name}"
        if key in _STRUCT_DEFS:
            sdef = _STRUCT_DEFS[key]
            return (sdef.total_size, sdef.alignment)
        raise UnsupportedTypeError(
            f"Struct '{key}' not yet defined. Structs must be defined before use."
        )
    if ctype.name in _SCALAR_SIZE_ALIGN:
        return _SCALAR_SIZE_ALIGN[ctype.name]
    raise UnsupportedTypeError(f"Cannot determine size/align for type '{ctype.name}'")


def compute_struct_layout(sdef: StructDef):
    """Compute field offsets, total size, and alignment for a struct.

    Follows gcc x86-64 LP64 ABI rules:
    - Each field aligned to its natural alignment
    - Struct alignment = max alignment of all fields
    - Struct size padded to multiple of struct alignment

    Mutates sdef in place.
    """
    offset = 0
    max_align = 1

    for f in sdef.fields:
        sz, al = type_size_align(f.c_type)
        f.size = sz
        f.align = al
        # Align the current offset
        if al > 0 and offset % al != 0:
            offset = ((offset + al - 1) // al) * al
        f.offset = offset
        offset += sz
        max_align = max(max_align, al)

    sdef.alignment = max_align
    # Pad to alignment
    if max_align > 0 and offset % max_align != 0:
        offset = ((offset + max_align - 1) // max_align) * max_align
    sdef.total_size = offset
