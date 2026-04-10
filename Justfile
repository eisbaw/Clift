# Clift common commands

# Build all Lean code (libraries + generated + examples)
build:
    lake build

# Build only the core library (no generated code or examples)
build-lib:
    lake build Clift

# Fetch Mathlib cache (run once after clone or Mathlib update)
setup:
    lake exe cache get

# Run CImporter on a .c file -> Generated/*.lean
# Usage: just import test/c_sources/gcd.c Gcd
import FILE NAME:
    mkdir -p test/clang_json Generated
    clang -Xclang -ast-dump=json -fsyntax-only {{FILE}} 2>/dev/null > test/clang_json/{{NAME}}.json
    python3 CImporter/import.py test/clang_json/{{NAME}}.json -o Generated/{{NAME}}.lean

# Re-import all known C sources
import-all:
    just import test/c_sources/gcd.c Gcd
    just import test/c_sources/max.c Max
    just import test/c_sources/swap.c Swap
    just import test/c_sources/list_length.c ListLength
    just import test/c_sources/rotate3.c Rotate3
    just import test/c_sources/div_test.c DivTest
    just import test/c_sources/signed_arith.c SignedArith
    just import test/c_sources/for_loop.c ForLoop
    just import test/c_sources/do_while.c DoWhile
    just import test/c_sources/switch_test.c SwitchTest
    just import test/c_sources/multi_call.c MultiCall
    just import test/c_sources/ring_buffer.c RingBuffer

# Run CImporter Python unit tests
test-importer:
    python3 -m pytest CImporter/tests/ -v

# Snapshot test: re-import, diff against expected output
test-snapshots:
    @echo "Checking CImporter output against expected snapshots..."
    just import test/c_sources/gcd.c Gcd && diff Generated/Gcd.lean test/expected/Gcd.lean
    just import test/c_sources/max.c Max && diff Generated/Max.lean test/expected/Max.lean

# Differential test: struct layout matches gcc sizeof/offsetof
test-struct-layout:
    python3 test/test_struct_layout.py

# End-to-end: importer snapshots pass AND all Lean code builds (proofs check)
e2e: test-importer test-snapshots test-struct-layout build

# Dump clang JSON AST for inspection
clang-dump FILE:
    clang -Xclang -ast-dump=json -fsyntax-only {{FILE}} | jq .

# Clean Lake build artifacts
clean:
    lake clean

# Show project status
status:
    @echo "=== Backlog ==="
    backlog board --plain 2>/dev/null || echo "(no tasks yet)"
    @echo ""
    @echo "=== Build ==="
    lake build 2>&1 | tail -5
