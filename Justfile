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
    just import test/c_sources/rtos_queue.c RtosQueue
    just import test/c_sources/sha256_core.c Sha256Core
    just import test/c_sources/uart_driver.c UartDriver
    just import test/c_sources/packet_parser.c PacketParser
    just import test/c_sources/sel4_cap.c Sel4Cap
    just import test/c_sources/hash_table.c HashTable
    just import test/c_sources/mem_alloc.c MemAlloc
    just import test/c_sources/rbtree.c Rbtree
    just import test/c_sources/state_machine.c StateMachine
    just import test/c_sources/priority_queue.c PriorityQueue
    just import test/c_sources/dma_buffer.c DmaBuffer

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

# Integer promotion audit tests
test-int-promotion:
    python3 -m pytest test/test_int_promotion.py -v

# Memory model UB audit tests
test-memory-ub:
    python3 -m pytest test/test_memory_model_ub.py -v

# CImporter fuzz testing (55 random programs)
test-fuzz:
    python3 test/fuzz_cimporter.py --count 55 --seed 42

# End-to-end: importer snapshots pass AND all Lean code builds (proofs check)
e2e: test-importer test-snapshots test-struct-layout test-int-promotion test-memory-ub build

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

# Nightly verification: full rebuild + sorry count tracking + regression alert
nightly:
    #!/usr/bin/env bash
    set -euo pipefail
    echo "=== Nightly Verification $(date -u +%Y-%m-%dT%H:%M:%SZ) ==="

    # 1. Full build
    lake build

    # 2. Count sorry
    mkdir -p metrics
    SORRY_COUNT=$(grep -rn "sorry" Clift/ Examples/ Generated/ --include="*.lean" \
      | grep -v "^.*:.*--" \
      | grep -v "sorry-free" \
      | grep -v "no sorry" \
      | grep -v "zero sorry" \
      | grep -v "Sorry" \
      | grep -v "#print axioms" \
      | grep -c "sorry" || true)
    TIMESTAMP=$(date -u +%Y-%m-%dT%H:%M:%SZ)
    COMMIT=$(git rev-parse --short HEAD 2>/dev/null || echo "unknown")
    echo "${TIMESTAMP} ${COMMIT} ${SORRY_COUNT}" >> metrics/sorry-count.log
    echo "Sorry count: ${SORRY_COUNT}"

    # 3. Alert if sorry count increased
    if [ $(wc -l < metrics/sorry-count.log) -gt 1 ]; then
      PREV_COUNT=$(tail -2 metrics/sorry-count.log | head -1 | awk '{print $3}')
      if [ "${SORRY_COUNT}" -gt "${PREV_COUNT}" ] 2>/dev/null; then
        echo "ALERT: Sorry count INCREASED: ${PREV_COUNT} -> ${SORRY_COUNT}"
        exit 1
      elif [ "${SORRY_COUNT}" -lt "${PREV_COUNT}" ]; then
        echo "Progress: sorry count decreased ${PREV_COUNT} -> ${SORRY_COUNT}"
      else
        echo "Stable: sorry count unchanged at ${SORRY_COUNT}"
      fi
    fi

    echo ""
    echo "=== Sorry count history ==="
    cat metrics/sorry-count.log
    echo ""
    echo "=== Nightly verification complete ==="

# Lint: check for common proof quality issues
lint:
    #!/usr/bin/env bash
    set -euo pipefail
    ISSUES=0
    echo "=== Clift Lint ==="

    # 1. Tautological postconditions (x = x pattern in FuncSpec post)
    echo ""
    echo "--- Tautological FuncSpec postconditions ---"
    TAUT=$(grep -n "post := fun" Examples/ -r --include="*.lean" -A5 \
      | grep -P '\.\w+ =\s*$' -A1 \
      | grep -P '^\s+.*\.\1\s*$' 2>/dev/null | wc -l || true)
    # Simpler check: find validHoare_weaken_trivial_post usage
    WEAKEN=$(grep -rn "validHoare_weaken_trivial_post" Examples/ --include="*.lean" \
      | grep -v "^.*:.*--" \
      | grep -v "private theorem validHoare_weaken_trivial_post" \
      | grep -c "validHoare_weaken_trivial_post" || true)
    if [ "$WEAKEN" -gt 0 ]; then
      echo "  WARN: $WEAKEN proofs use validHoare_weaken_trivial_post (trivializes postcondition)"
      grep -rn "validHoare_weaken_trivial_post" Examples/ --include="*.lean" \
        | grep -v "^.*:.*--" \
        | grep -v "private theorem validHoare_weaken_trivial_post"
      ISSUES=$((ISSUES + WEAKEN))
    else
      echo "  OK: No trivial postcondition weakening found"
    fi

    # 2. Sorry count
    echo ""
    echo "--- Sorry in proof files ---"
    SORRY=$(grep -rn "^\s*sorry" Examples/ --include="*.lean" | grep -c "sorry" || true)
    if [ "$SORRY" -gt 0 ]; then
      echo "  WARN: $SORRY sorry remaining in Examples/"
      ISSUES=$((ISSUES + SORRY))
    else
      echo "  OK: Zero sorry in Examples/"
    fi

    # 3. Sorry in core library (should always be 0)
    echo ""
    echo "--- Sorry in core library ---"
    LIB_SORRY=$(grep -rn "^\s*sorry" Clift/ --include="*.lean" | grep -c "sorry" || true)
    if [ "$LIB_SORRY" -gt 0 ]; then
      echo "  FAIL: $LIB_SORRY sorry in Clift/ (core library must be sorry-free)"
      grep -rn "^\s*sorry" Clift/ --include="*.lean"
      ISSUES=$((ISSUES + LIB_SORRY))
    else
      echo "  OK: Core library sorry-free"
    fi

    echo ""
    echo "=== Lint: $ISSUES issues found ==="
    if [ "$ISSUES" -gt 0 ]; then exit 1; fi

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

# Regression suite: comprehensive CI check (task 0166)
# Runs: sorry count, axiom audit, CImporter tests, snapshot tests,
#        fuzz tests, struct layout, int promotion, memory UB, lake build
regression:
    #!/usr/bin/env bash
    set -euo pipefail
    PASS=0
    FAIL=0
    TOTAL=0

    run_check() {
      local name="$1"
      shift
      TOTAL=$((TOTAL + 1))
      echo ""
      echo "=== [$TOTAL] $name ==="
      if "$@" 2>&1; then
        echo "  PASS: $name"
        PASS=$((PASS + 1))
      else
        echo "  FAIL: $name"
        FAIL=$((FAIL + 1))
      fi
    }

    echo "========================================="
    echo "  Clift Regression Suite"
    echo "========================================="

    # 1. Sorry count (informational, does not block)
    run_check "Sorry count" just sorry-count

    # 2. Axiom audit: check no sorry-based axioms in core library
    TOTAL=$((TOTAL + 1))
    echo ""
    echo "=== [$TOTAL] Axiom audit (no sorryAx in Clift/) ==="
    AXIOM_SORRY=$(grep -rn "sorryAx" Clift/ --include="*.lean" | grep -v "^.*:.*--" | wc -l || true)
    if [ "$AXIOM_SORRY" -eq 0 ]; then
      echo "  PASS: No sorryAx in library code"
      PASS=$((PASS + 1))
    else
      echo "  FAIL: Found $AXIOM_SORRY sorryAx references"
      FAIL=$((FAIL + 1))
    fi

    # 3. CImporter unit tests
    run_check "CImporter unit tests" python3 -m pytest CImporter/tests/ -v

    # 4. Snapshot tests
    run_check "Snapshot tests" just test-snapshots

    # 5. Struct layout tests
    run_check "Struct layout tests" just test-struct-layout

    # 6. Integer promotion tests
    run_check "Int promotion tests" just test-int-promotion

    # 7. Memory model UB tests
    run_check "Memory UB tests" just test-memory-ub

    # 8. Fuzz tests
    run_check "Fuzz tests (55 programs)" just test-fuzz

    # 9. Lake build (the big one -- checks all proofs)
    run_check "Lake build (full)" lake build

    echo ""
    echo "========================================="
    echo "  Results: $PASS/$TOTAL passed, $FAIL failed"
    echo "========================================="

    if [ "$FAIL" -gt 0 ]; then
      echo "REGRESSION DETECTED"
      exit 1
    fi
    echo "ALL CHECKS PASSED"
