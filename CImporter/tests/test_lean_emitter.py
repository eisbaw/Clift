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

    def test_has_div_guard_on_modulo(self):
        """task-0059: modulo in gcd should get a division-by-zero guard."""
        lean = _load_and_emit("Gcd")
        assert ".guard" in lean
        # The guard should check that divisor (b) is nonzero
        assert u"s.locals.b \u2260 0" in lean

    def test_has_proc_env(self):
        lean = _load_and_emit("Gcd")
        assert '"gcd"' in lean


class TestDivTestEmission:
    """task-0059: Division and modulo UB guards."""

    def test_div_has_guard(self):
        lean = _load_and_emit("DivTest")
        assert ".guard" in lean

    def test_div_guard_checks_divisor_nonzero(self):
        lean = _load_and_emit("DivTest")
        # Both safe_div and safe_mod should guard that b != 0
        assert u"s.locals.b \u2260 0" in lean

    def test_has_both_functions(self):
        lean = _load_and_emit("DivTest")
        assert "safe_div_body" in lean
        assert "safe_mod_body" in lean


class TestSignedArithEmission:
    """task-0072: Signed integer overflow UB guards."""

    def test_signed_add_has_overflow_guard(self):
        lean = _load_and_emit("SignedArith")
        assert "signed_add_body" in lean
        # Should have overflow guard with toBitVec.toInt
        assert "toBitVec.toInt" in lean

    def test_signed_add_checks_range(self):
        lean = _load_and_emit("SignedArith")
        # INT_MIN = -2147483648, INT_MAX = 2147483647
        assert "-2147483648" in lean
        assert "2147483647" in lean

    def test_signed_sub_has_guard(self):
        lean = _load_and_emit("SignedArith")
        assert "signed_sub_body" in lean

    def test_signed_mul_has_guard(self):
        lean = _load_and_emit("SignedArith")
        assert "signed_mul_body" in lean

    def test_signed_div_has_divzero_guard(self):
        lean = _load_and_emit("SignedArith")
        # Signed division has both div-by-zero and INT_MIN/-1 guards
        assert u"s.locals.b \u2260 0" in lean

    def test_signed_div_has_int_min_neg1_guard(self):
        lean = _load_and_emit("SignedArith")
        # INT_MIN / -1 guard: not (a == 2^31 and b == 2^32 - 1)
        assert "2147483648" in lean  # INT_MIN as unsigned
        assert "4294967295" in lean  # -1 as unsigned


class TestForLoopEmission:
    """task-0077: for loop desugaring."""

    def test_for_loop_becomes_while(self):
        lean = _load_and_emit("ForLoop")
        assert ".while" in lean

    def test_has_init_and_step(self):
        lean = _load_and_emit("ForLoop")
        # Init: i := 0
        assert "i := 0" in lean
        # Step: i := i + 1
        assert "i := (s.locals.i + 1)" in lean

    def test_has_sum_body(self):
        lean = _load_and_emit("ForLoop")
        assert "sum_to_n_body" in lean

    def test_has_local_i(self):
        lean = _load_and_emit("ForLoop")
        assert "i : UInt32" in lean


class TestDoWhileEmission:
    """task-0077: do-while desugaring."""

    def test_do_while_has_body_before_loop(self):
        lean = _load_and_emit("DoWhile")
        # The body should appear before the while
        lines = lean.split('\n')
        # Find first occurrence of count + 1 (body) and while
        body_line = next(i for i, l in enumerate(lines) if "count + 1" in l)
        while_line = next(i for i, l in enumerate(lines) if ".while" in l)
        assert body_line < while_line, "do-while body should appear before the while loop"

    def test_has_div_guard_in_do_while(self):
        lean = _load_and_emit("DoWhile")
        # n / 10 should have a guard (trivially true but correct)
        assert ".guard" in lean


class TestSwitchEmission:
    """task-0077: switch desugaring to nested if/else."""

    def test_switch_becomes_cond(self):
        lean = _load_and_emit("SwitchTest")
        assert ".cond" in lean

    def test_has_case_conditions(self):
        lean = _load_and_emit("SwitchTest")
        # Should have equality checks for case values
        assert "s.locals.x = 0" in lean
        assert "s.locals.x = 1" in lean
        assert "s.locals.x = 2" in lean

    def test_has_default_branch(self):
        lean = _load_and_emit("SwitchTest")
        # Default: result = 999
        assert "999" in lean

    def test_has_classify_body(self):
        lean = _load_and_emit("SwitchTest")
        assert "classify_body" in lean
