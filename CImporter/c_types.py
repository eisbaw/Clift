"""C type representation for the CImporter.

Maps clang's type representations to Lean 4 types.
This module is in the TCB — incorrect type mapping invalidates all downstream proofs.

Supported types (StrictC subset):
  - uint8_t, uint16_t, uint32_t, uint64_t (unsigned integers)
  - int8_t, int16_t, int32_t, int64_t (signed integers)
  - void (return type only)
  - _Bool / bool

Unsupported (rejected with clear error):
  - float, double (no floating point in Phase 1)
  - pointers (Phase 3)
  - structs (Phase 3)
  - arrays, VLAs
"""

from dataclasses import dataclass
from typing import Optional
import logging

log = logging.getLogger(__name__)


@dataclass(frozen=True)
class CType:
    """A C type as seen by the importer."""
    name: str        # Canonical name: "uint32_t", "int64_t", "void", "bool"
    signed: bool     # True for int8_t..int64_t
    bits: int        # Bit width (0 for void)

    @property
    def lean_type(self) -> str:
        """Lean 4 type name for this C type."""
        if self.name == "void":
            return "Unit"
        if self.name == "bool":
            return "Bool"
        return f"UInt{self.bits}" if not self.signed else f"Int{self.bits}"

    @property
    def lean_default(self) -> str:
        """Lean 4 default value for this type."""
        if self.name == "void":
            return "()"
        if self.name == "bool":
            return "false"
        return "0"

    @property
    def is_unsigned(self) -> bool:
        return not self.signed and self.name != "void" and self.name != "bool"


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

    # Check for unsupported types and give clear errors
    for bad in ("float", "double", "long double"):
        if bad in desugared or bad in qual:
            raise UnsupportedTypeError(
                f"Floating point type '{qual}' not supported (StrictC restriction). "
                f"Only integer types are allowed in Phase 1."
            )
    if "*" in qual or "*" in desugared:
        raise UnsupportedTypeError(
            f"Pointer type '{qual}' not yet supported (Phase 3). "
        )

    raise UnsupportedTypeError(
        f"Unknown C type: qualType='{qual}', desugaredQualType='{desugared}'. "
        f"Supported types: {sorted(_CLANG_TYPE_MAP.keys())}"
    )


def return_type_from_qual(qual_type_str: str) -> CType:
    """Extract return type from a function's qualType string.

    E.g. "uint32_t (uint32_t, uint32_t)" -> UINT32

    Args:
        qual_type_str: The function's qualType from clang JSON.

    Returns:
        The return CType.
    """
    # Function qualType format: "return_type (param_types)"
    ret_str = qual_type_str.split("(")[0].strip()
    if ret_str in _CLANG_TYPE_MAP:
        return _CLANG_TYPE_MAP[ret_str]
    raise UnsupportedTypeError(f"Unknown return type: '{ret_str}'")
