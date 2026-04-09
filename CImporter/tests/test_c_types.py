"""Tests for CImporter c_types module."""

import pytest
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from CImporter.c_types import (
    parse_clang_type, return_type_from_qual, UnsupportedTypeError,
    UINT8, UINT16, UINT32, UINT64, INT8, INT16, INT32, INT64, VOID, BOOL,
)


class TestParseClangType:
    def test_unsigned_int_desugared(self):
        node = {"desugaredQualType": "unsigned int", "qualType": "uint32_t"}
        assert parse_clang_type(node) == UINT32

    def test_unsigned_char(self):
        node = {"desugaredQualType": "unsigned char", "qualType": "uint8_t"}
        assert parse_clang_type(node) == UINT8

    def test_unsigned_short(self):
        node = {"desugaredQualType": "unsigned short", "qualType": "uint16_t"}
        assert parse_clang_type(node) == UINT16

    def test_unsigned_long(self):
        node = {"desugaredQualType": "unsigned long", "qualType": "uint64_t"}
        assert parse_clang_type(node) == UINT64

    def test_signed_int(self):
        node = {"desugaredQualType": "int", "qualType": "int32_t"}
        assert parse_clang_type(node) == INT32

    def test_int_qualtype_only(self):
        """When there's no desugared form, use qualType."""
        node = {"qualType": "int"}
        assert parse_clang_type(node) == INT32

    def test_void(self):
        node = {"qualType": "void"}
        assert parse_clang_type(node) == VOID

    def test_bool(self):
        node = {"desugaredQualType": "_Bool", "qualType": "bool"}
        assert parse_clang_type(node) == BOOL

    def test_float_rejected(self):
        with pytest.raises(UnsupportedTypeError, match="Floating point"):
            parse_clang_type({"qualType": "float"})

    def test_double_rejected(self):
        with pytest.raises(UnsupportedTypeError, match="Floating point"):
            parse_clang_type({"qualType": "double"})

    def test_pointer_to_scalar(self):
        """Phase 3a: pointers to scalar types are now supported."""
        t = parse_clang_type({"qualType": "unsigned int *", "desugaredQualType": "unsigned int *"})
        assert t.is_pointer
        assert t.pointee.lean_type == "UInt32"
        assert t.lean_type == "Ptr UInt32"

    def test_pointer_to_unsupported_rejected(self):
        with pytest.raises(UnsupportedTypeError, match="Pointer to unsupported"):
            parse_clang_type({"qualType": "struct foo *", "desugaredQualType": "struct foo *"})

    def test_unknown_rejected(self):
        with pytest.raises(UnsupportedTypeError, match="Unknown C type"):
            parse_clang_type({"qualType": "struct foo"})


class TestReturnType:
    def test_uint32_return(self):
        assert return_type_from_qual("uint32_t (uint32_t, uint32_t)") == UINT32

    def test_void_return(self):
        assert return_type_from_qual("void (int)") == VOID

    def test_int_return(self):
        assert return_type_from_qual("int ()") == INT32


class TestLeanType:
    def test_uint32_lean(self):
        assert UINT32.lean_type == "UInt32"

    def test_int64_lean(self):
        assert INT64.lean_type == "Int64"

    def test_void_lean(self):
        assert VOID.lean_type == "Unit"

    def test_bool_lean(self):
        assert BOOL.lean_type == "Bool"

    def test_default_values(self):
        assert UINT32.lean_default == "0"
        assert VOID.lean_default == "()"
        assert BOOL.lean_default == "false"
