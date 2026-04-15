"""Tests for the tautological postcondition linter."""

import sys
from pathlib import Path

# Add parent to path so we can import the module
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from tautological import (
    _normalize_whitespace,
    _is_tautological_eq,
    _find_funcspec_blocks,
    _check_post_tautological,
    _check_purely_tautological,
    find_trivial_weakening,
    scan_file,
    Finding,
)


def test_normalize_whitespace():
    assert _normalize_whitespace("  a  b  c  ") == "a b c"
    assert _normalize_whitespace("a\n  b") == "a b"


def test_is_tautological_eq():
    assert _is_tautological_eq("x.count", "x.count")
    assert _is_tautological_eq("x.count ", " x.count")
    assert not _is_tautological_eq("x.count", "y.count")


def test_find_funcspec_simple():
    content = """
def my_spec : FuncSpec ProgramState where
  pre := fun s => True
  post := fun r s =>
    r = Except.ok () ->
    s.locals.ret__val = 0
"""
    blocks = _find_funcspec_blocks(content, Path("test.lean"))
    assert len(blocks) == 1
    name, line, post = blocks[0]
    assert name == "my_spec"
    assert "ret__val = 0" in post


def test_tautological_direct():
    post = """  post := fun r s =>
    r = Except.ok () ->
    (hVal s.globals.rawHeap s.locals.rb).count =
      (hVal s.globals.rawHeap s.locals.rb).count"""
    result = _check_post_tautological(post)
    assert result is not None
    assert "tautological" in result


def test_tautological_let_bound():
    post = """  post := fun r s =>
    r = Except.ok () ->
    let rb := hVal s.globals.rawHeap s.locals.rb
    rb.head = rb.head ∧ rb.tail = rb.tail"""
    result = _check_post_tautological(post)
    assert result is not None
    assert "let-bound" in result


def test_not_tautological():
    post = """  post := fun r s =>
    r = Except.ok () ->
    s.locals.ret__val = 0"""
    result = _check_post_tautological(post)
    assert result is None


def test_purely_tautological():
    post = """  post := fun r s =>
    r = Except.ok () ->
    (hVal s.globals.rawHeap s.locals.rb).count =
      (hVal s.globals.rawHeap s.locals.rb).count"""
    assert _check_purely_tautological(post) is True


def test_not_purely_tautological():
    post = """  post := fun r s =>
    r = Except.ok () ->
    s.locals.ret__val = 0 ∧
    (hVal s.globals.rawHeap s.locals.rb).count =
      (hVal s.globals.rawHeap s.locals.rb).count"""
    # Has a non-tautological conjunct
    assert _check_purely_tautological(post) is False


def test_trivial_weakening_in_code():
    content = """
theorem foo : bar := by
  apply validHoare_weaken_trivial_post
  exact baz
"""
    findings = find_trivial_weakening(content, Path("test.lean"))
    assert len(findings) == 1
    assert findings[0].kind == "trivial_weakening"


def test_trivial_weakening_in_comment():
    content = """
-- Don't use validHoare_weaken_trivial_post
theorem foo : bar := by exact baz
"""
    findings = find_trivial_weakening(content, Path("test.lean"))
    assert len(findings) == 0


def test_trivial_weakening_in_block_comment():
    content = """/-
Tautological postconditions (grep for validHoare_weaken_trivial_post)
-/
theorem foo : bar := by exact baz
"""
    findings = find_trivial_weakening(content, Path("test.lean"))
    assert len(findings) == 0


def test_removed_comment_excluded():
    content = """
-- REMOVED: validHoare_weaken_trivial_post
"""
    findings = find_trivial_weakening(content, Path("test.lean"))
    assert len(findings) == 0
