"""Tests for CImporter ast_parser module."""

import pytest
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from CImporter.ast_parser import (
    parse_translation_unit, StrictCViolation, load_ast,
)
from CImporter.c_types import UINT32


PROJECT_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def _load_test_json(name: str) -> dict:
    """Load a test clang JSON file."""
    path = os.path.join(PROJECT_ROOT, "test", "clang_json", f"{name}.json")
    if not os.path.exists(path):
        pytest.skip(f"Test JSON not found: {path}")
    return load_ast(path)


class TestParseMax:
    """Tests against max.c clang JSON."""

    def test_parse_one_function(self):
        ast = _load_test_json("Max")
        tu = parse_translation_unit(ast)
        assert len(tu.functions) == 1

    def test_function_name(self):
        ast = _load_test_json("Max")
        tu = parse_translation_unit(ast)
        assert tu.functions[0].name == "max"

    def test_return_type(self):
        ast = _load_test_json("Max")
        tu = parse_translation_unit(ast)
        assert tu.functions[0].return_type == UINT32

    def test_params(self):
        ast = _load_test_json("Max")
        tu = parse_translation_unit(ast)
        func = tu.functions[0]
        assert len(func.params) == 2
        assert func.params[0].name == "a"
        assert func.params[0].c_type == UINT32
        assert func.params[1].name == "b"
        assert func.params[1].c_type == UINT32

    def test_body_is_compound(self):
        ast = _load_test_json("Max")
        tu = parse_translation_unit(ast)
        assert tu.functions[0].body.kind == "compound"

    def test_body_has_return(self):
        ast = _load_test_json("Max")
        tu = parse_translation_unit(ast)
        body = tu.functions[0].body
        # The compound should contain a return statement
        assert len(body.stmts) == 1
        assert body.stmts[0].kind == "return"

    def test_return_has_ternary(self):
        ast = _load_test_json("Max")
        tu = parse_translation_unit(ast)
        ret = tu.functions[0].body.stmts[0]
        assert ret.expr.kind == "ternary"

    def test_ternary_condition(self):
        ast = _load_test_json("Max")
        tu = parse_translation_unit(ast)
        ternary = tu.functions[0].body.stmts[0].expr
        # condition is a > b
        assert ternary.lhs.kind == "binop"
        assert ternary.lhs.op == ">"

    def test_no_locals(self):
        """max() has no local variables (only params)."""
        ast = _load_test_json("Max")
        tu = parse_translation_unit(ast)
        assert len(tu.functions[0].locals) == 0


class TestParseGcd:
    """Tests against gcd.c clang JSON."""

    def test_parse_one_function(self):
        ast = _load_test_json("Gcd")
        tu = parse_translation_unit(ast)
        assert len(tu.functions) == 1

    def test_function_name(self):
        ast = _load_test_json("Gcd")
        tu = parse_translation_unit(ast)
        assert tu.functions[0].name == "gcd"

    def test_has_while_loop(self):
        ast = _load_test_json("Gcd")
        tu = parse_translation_unit(ast)
        body = tu.functions[0].body
        # First statement should be while
        assert body.stmts[0].kind == "while"

    def test_has_local_t(self):
        ast = _load_test_json("Gcd")
        tu = parse_translation_unit(ast)
        func = tu.functions[0]
        assert len(func.locals) == 1
        assert func.locals[0].name == "t"
        assert func.locals[0].c_type == UINT32

    def test_while_condition(self):
        ast = _load_test_json("Gcd")
        tu = parse_translation_unit(ast)
        while_stmt = tu.functions[0].body.stmts[0]
        # Condition is b != 0
        assert while_stmt.condition.kind == "binop"
        assert while_stmt.condition.op == "!="

    def test_while_body_has_three_stmts(self):
        ast = _load_test_json("Gcd")
        tu = parse_translation_unit(ast)
        while_stmt = tu.functions[0].body.stmts[0]
        loop_body = while_stmt.loop_body
        assert loop_body.kind == "compound"
        # 3 statements: t = b, b = a % b, a = t
        assert len(loop_body.stmts) == 3

    def test_return_at_end(self):
        ast = _load_test_json("Gcd")
        tu = parse_translation_unit(ast)
        body = tu.functions[0].body
        assert body.stmts[1].kind == "return"


class TestStrictCRejection:
    """Test that unsupported constructs are rejected."""

    def _make_minimal_ast(self, func_inner):
        """Build a minimal clang AST with a function containing given inner nodes."""
        return {
            "kind": "TranslationUnitDecl",
            "inner": [{
                "kind": "FunctionDecl",
                "name": "test",
                "type": {"qualType": "void ()"},
                "inner": [
                    {
                        "kind": "CompoundStmt",
                        "inner": func_inner,
                    }
                ],
            }]
        }

    def test_goto_rejected(self):
        ast = self._make_minimal_ast([{"kind": "GotoStmt"}])
        with pytest.raises(StrictCViolation, match="goto"):
            parse_translation_unit(ast)

    def test_address_of_rejected(self):
        ast = self._make_minimal_ast([{
            "kind": "UnaryOperator",
            "opcode": "&",
            "inner": [{
                "kind": "DeclRefExpr",
                "referencedDecl": {"name": "x"},
            }],
        }])
        with pytest.raises(StrictCViolation, match="Address-of"):
            parse_translation_unit(ast)
