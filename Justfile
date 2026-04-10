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
    just import test/c_sources/sum_array.c SumArray
    just import test/c_sources/enum_typedef_global.c EnumTypedefGlobal
    just import test/c_sources/ring_buffer_ext.c RingBufferExt
    just import test/c_sources/bitwise.c Bitwise
    just import test/c_sources/casts_sizeof.c CastsSizeof
    just import test/c_sources/unions_void.c UnionsVoid
    just import test/c_sources/strings.c Strings

# Multi-file import: process multiple .c files into a Lean module set
# Usage: just multi-import MultiProject test/c_sources/multi_file/helper.c test/c_sources/multi_file/main.c
multi-import PROJECT *FILES:
    #!/usr/bin/env bash
    set -euo pipefail
    mkdir -p test/clang_json Generated/{{PROJECT}}
    json_args=""
    for f in {{FILES}}; do
        name=$(basename "$f" .c)
        name="$(tr '[:lower:]' '[:upper:]' <<< ${name:0:1})${name:1}"
        clang -Xclang -ast-dump=json -fsyntax-only -I "$(dirname "$f")" "$f" 2>/dev/null > "test/clang_json/${name}.json"
        json_args="$json_args test/clang_json/${name}.json"
    done
    python3 CImporter/multi_import.py --project {{PROJECT}} $json_args -o Generated/{{PROJECT}}

# Import the multi-file test project
import-multi-test:
    just multi-import MultiProject test/c_sources/multi_file/helper.c test/c_sources/multi_file/main.c

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

# Run proof engine (extract sorry, attempt automated proof)
# Usage: just prove Examples/RingBufferProof.lean
prove FILE:
    python3 clift-prove-by-claudecode {{FILE}} --project-dir . -v

# Dry-run proof engine (extract only, no proof attempts)
prove-dry FILE:
    python3 clift-prove-by-claudecode {{FILE}} --project-dir . --dry-run -v

# CI: full verification pipeline (same checks as GitHub Actions)
ci:
    #!/usr/bin/env bash
    set -euo pipefail
    echo "=== CI: Sorry check ==="
    SORRY_COUNT=$(grep -rn "sorry" Clift/ Examples/ Generated/ --include="*.lean" \
      | grep -v "^.*:.*--" \
      | grep -v "sorry-free" \
      | grep -v "no sorry" \
      | grep -v "zero sorry" \
      | grep -v "Sorry" \
      | grep -v "#print axioms" \
      | grep -c "sorry" || true)
    echo "Sorry count: $SORRY_COUNT"
    if [ "$SORRY_COUNT" -gt 0 ]; then
      echo "FAIL: Found $SORRY_COUNT sorry in code"
      exit 1
    fi
    echo ""
    echo "=== CI: CImporter unit tests ==="
    python3 -m pytest CImporter/tests/ -v
    echo ""
    echo "=== CI: Snapshot tests ==="
    just test-snapshots
    echo ""
    echo "=== CI: Struct layout tests ==="
    just test-struct-layout
    echo ""
    echo "=== CI: Lake build (all targets) ==="
    lake build
    echo ""
    echo "=== CI: All checks passed ==="

# Sorry count: quick check for sorry in library code
sorry-count:
    #!/usr/bin/env bash
    COUNT=$(grep -rn "sorry" Clift/ Examples/ Generated/ --include="*.lean" \
      | grep -v "^.*:.*--" \
      | grep -v "sorry-free" \
      | grep -v "no sorry" \
      | grep -v "zero sorry" \
      | grep -v "Sorry" \
      | grep -v "#print axioms" \
      | grep -c "sorry" || true)
    echo "Sorry count: $COUNT"
    if [ "$COUNT" -gt 0 ]; then
      grep -rn "sorry" Clift/ Examples/ Generated/ --include="*.lean" \
        | grep -v "^.*:.*--" \
        | grep -v "sorry-free" \
        | grep -v "no sorry" \
        | grep -v "zero sorry" \
        | grep -v "Sorry" \
        | grep -v "#print axioms" \
        | grep "sorry"
    fi

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
