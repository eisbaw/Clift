"""Tests for CImporter lean_emitter module."""

import pytest
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from CImporter.ast_parser import load_ast, parse_translation_unit
from CImporter.lean_emitter import emit_lean


PROJECT_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def _load_and_emit(name: str) -> str:
    path = os.path.join(PROJECT_ROOT, "test", "clang_json", f"{name}.json")
    if not os.path.exists(path):
        pytest.skip(f"Test JSON not found: {path}")
    ast = load_ast(path)
    tu = parse_translation_unit(ast)
    return emit_lean(tu, name.capitalize())


class TestMaxEmission:
    def test_has_import(self):
        lean = _load_and_emit("Max")
        assert "import Clift.CSemantics" in lean

    def test_uses_library_globals(self):
        lean = _load_and_emit("Max")
        # Should use the library's Globals via CState, not redefine it
        assert "structure Globals" not in lean
        assert "CState Locals" in lean

    def test_has_locals(self):
        lean = _load_and_emit("Max")
        assert "structure Locals" in lean
        # Should have fields for a, b, and ret__val
        assert "a : UInt32" in lean
        assert "b : UInt32" in lean
        assert "ret__val : UInt32" in lean

    def test_has_program_state(self):
        lean = _load_and_emit("Max")
        assert "abbrev ProgramState" in lean

    def test_has_max_body(self):
        lean = _load_and_emit("Max")
        assert "def max_body : CSimpl ProgramState" in lean

    def test_has_catch_throw_pattern(self):
        lean = _load_and_emit("Max")
        assert ".catch" in lean
        assert ".throw" in lean

    def test_has_ternary_as_if(self):
        lean = _load_and_emit("Max")
        # The ternary a > b ? a : b is emitted as if-then-else inside basic
        assert "if decide" in lean
        assert "s.locals.a" in lean
        assert "s.locals.b" in lean

    def test_has_proc_env(self):
        lean = _load_and_emit("Max")
        assert "def procEnv : ProcEnv ProgramState" in lean
        assert '"max"' in lean


class TestGcdEmission:
    def test_has_while(self):
        lean = _load_and_emit("Gcd")
        assert ".while" in lean

    def test_has_local_t(self):
        lean = _load_and_emit("Gcd")
        assert "t : UInt32" in lean

    def test_has_gcd_body(self):
        lean = _load_and_emit("Gcd")
        assert "def gcd_body : CSimpl ProgramState" in lean

    def test_has_modulo(self):
        lean = _load_and_emit("Gcd")
        # Should have % operation
        assert "%" in lean

    def test_has_proc_env(self):
        lean = _load_and_emit("Gcd")
        assert '"gcd"' in lean
