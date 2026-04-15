# Clift commands

# Build all Lean code
build:
    lake build

# Build with flock to prevent concurrent builds (use from agents)
build-lock MODULE:
    flock --timeout 600 /tmp/clift-build.lock lake build {{MODULE}}

# Build only core library (no examples)
build-lib:
    lake build Clift

# Clean Lake build artifacts
clean:
    lake clean

# Import a C file: just import test/c_sources/gcd.c Gcd
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

# Multi-file import: just multi-import MultiProject test/c_sources/multi_file/helper.c test/c_sources/multi_file/main.c
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

# Generate projection simp lemmas for a Generated file
gen-projections FILE *ARGS:
    python3 -m CImporter.proof_engine.gen_projections {{FILE}} {{ARGS}}

# Regenerate all projection files
gen-projections-all:
    python3 -m CImporter.proof_engine.gen_projections Generated/Swap.lean -o Generated/SwapProjections.lean
    python3 -m CImporter.proof_engine.gen_projections Generated/RingBufferExt.lean -o Generated/RingBufferExtProjections.lean

# Dump clang JSON AST for inspection
clang-dump FILE:
    clang -Xclang -ast-dump=json -fsyntax-only {{FILE}} | jq .

# Run proof engine: just prove Examples/RingBufferProof.lean
prove FILE:
    python3 clift-prove-by-claudecode {{FILE}} --project-dir . -v

# --- Testing ---

# CImporter unit tests
test-importer:
    python3 -m pytest CImporter/tests/ -v

# Snapshot test: re-import and diff against expected
test-snapshots:
    @echo "Checking CImporter output against expected snapshots..."
    just import test/c_sources/gcd.c Gcd && diff Generated/Gcd.lean test/expected/Gcd.lean
    just import test/c_sources/max.c Max && diff Generated/Max.lean test/expected/Max.lean

# Struct layout: matches gcc sizeof/offsetof
test-struct-layout:
    python3 test/test_struct_layout.py

# Integer promotion audit
test-int-promotion:
    python3 -m pytest test/test_int_promotion.py -v

# Memory model UB audit
test-memory-ub:
    python3 -m pytest test/test_memory_model_ub.py -v

# CImporter fuzz testing (55 random programs)
test-fuzz:
    python3 test/fuzz_cimporter.py --count 55 --seed 42

# Audit tool unit tests
test-audit:
    python3 -m pytest tools/lint/tests/ -v

# Lint: tautological postconditions + proof quality
lint:
    python3 tools/lint/tautological.py

# --- CI (called by GitHub Actions and locally) ---

# Full CI pipeline
ci: ci-core-sorry ci-audit ci-importer build

# Core library must have zero sorry
ci-core-sorry:
    #!/usr/bin/env bash
    set -euo pipefail
    SORRY=$(grep -rn "^\s*sorry" Clift/ --include="*.lean" | grep -c "sorry" || true)
    if [ "$SORRY" -gt 0 ]; then
      echo "FAIL: Found $SORRY sorry in Clift/"
      grep -rn "^\s*sorry" Clift/ --include="*.lean"
      exit 1
    fi
    echo "Core library: zero sorry"

# Python audit (authoritative sorry count + proof quality checks)
ci-audit:
    python3 tools/lint/audit.py --skip-lake

# CImporter tests (unit + snapshot + struct layout + int promotion)
ci-importer:
    #!/usr/bin/env bash
    set -euo pipefail
    python3 -m pytest CImporter/tests/ -v
    just test-snapshots
    just test-struct-layout
    just test-int-promotion

# Build a specific proof module
ci-proof MODULE:
    lake build {{MODULE}}

# --- End-to-end ---

# End-to-end: all tests + full build
e2e: ci-importer test-memory-ub build

# Full audit: Python audit + semantic lint
audit:
    #!/usr/bin/env bash
    set -euo pipefail
    python3 tools/lint/audit.py --skip-lake
    echo ""
    echo "=== Bash sanity checks ==="
    CORE_SORRY=$(grep -rn "^\s*sorry" Clift/ --include="*.lean" 2>/dev/null | grep -c "sorry" || true)
    if [ "$CORE_SORRY" -gt 0 ]; then
      echo "  FAIL: $CORE_SORRY sorry in Clift/"
      exit 1
    fi
    echo "  OK: Core library sorry-free"
    echo ""
    echo "=== Axiom smuggling detection ==="
    CSIMP=$(grep -rn '@\[csimp\]' Clift/ Examples/ --include="*.lean" 2>/dev/null | grep -c '@\[csimp\]' || true)
    if [ "$CSIMP" -gt 0 ]; then
      echo "  FAIL: Found $CSIMP @[csimp] usage(s) in proof-critical code"
      grep -rn '@\[csimp\]' Clift/ Examples/ --include="*.lean"
      exit 1
    fi
    echo "  OK: No @[csimp] axiom smuggling"
    IMPL_BY=$(grep -rn '@\[implemented_by\]' Clift/ Examples/ --include="*.lean" 2>/dev/null | grep -c '@\[implemented_by\]' || true)
    if [ "$IMPL_BY" -gt 0 ]; then
      echo "  FAIL: Found $IMPL_BY @[implemented_by] usage(s) in proof-critical code"
      grep -rn '@\[implemented_by\]' Clift/ Examples/ --include="*.lean"
      exit 1
    fi
    echo "  OK: No @[implemented_by] axiom smuggling"
    echo ""
    echo "=== Vacuous precondition detection ==="
    VACUOUS=$(grep -rEn 'fun\s+\w+\s*=>\s*False' Examples/ --include="*.lean" 2>/dev/null | grep -v '^\s*--' | grep -c 'False' || true)
    if [ "$VACUOUS" -gt 0 ]; then
      echo "  FAIL: Found $VACUOUS vacuous precondition(s) (fun _ => False)"
      grep -rEn 'fun\s+\w+\s*=>\s*False' Examples/ --include="*.lean" | grep -v '^\s*--'
      exit 1
    fi
    echo "  OK: No vacuous preconditions detected"

# Count sorry in Examples/ (delegates to Python audit for accuracy)
sorry-count:
    #!/usr/bin/env bash
    set -euo pipefail
    COUNT=$(python3 tools/lint/audit.py --skip-lake 2>&1 | grep -oP 'sorry_count: \K[0-9]+')
    echo "sorry: $COUNT"

# Nightly: record sorry count to metrics log
nightly:
    #!/usr/bin/env bash
    set -euo pipefail
    COUNT=$(python3 tools/lint/audit.py --skip-lake 2>&1 | grep -oP 'sorry_count: \K[0-9]+')
    ENTRY="$(date -u +%Y-%m-%dT%H:%M:%SZ) $(git rev-parse --short HEAD) $COUNT"
    echo "$ENTRY" >> metrics/sorry-count.log
    echo "Recorded: $ENTRY"

# Semantic lint: per-module MetaM checks (best-effort, timeouts = skip)
lint-semantic MODULE="all":
    #!/usr/bin/env bash
    set -euo pipefail
    TIMEOUT=300
    MODULES=(GcdEndToEnd HashTable Swap DmaBuffer PacketParser MemAlloc RtosQueue \
             Sha256 UartDriver Sel4Cap StateMachine PriorityQueue \
             RBSimple RBLoops RBLoops2 RBRefinement)
    PASS=0; FAIL=0; SKIP=0
    if [ "{{MODULE}}" = "all" ]; then
      TARGETS=("${MODULES[@]}")
    else
      TARGETS=("{{MODULE}}")
    fi
    for M in "${TARGETS[@]}"; do
      echo -n "  Lint${M}... "
      pkill -f lean 2>/dev/null; sleep 1
      OUTPUT=$(timeout ${TIMEOUT} lake build -j1 "Tools.Lint.Lean.Lint${M}" 2>&1) || EXIT=$?
      EXIT=${EXIT:-0}
      if [ "$EXIT" -eq 124 ]; then
        echo "SKIP (timeout ${TIMEOUT}s)"
        SKIP=$((SKIP + 1))
      elif echo "$OUTPUT" | tail -1 | grep -q "successfully"; then
        echo "OK"
        PASS=$((PASS + 1))
      else
        echo "FAIL"
        echo "$OUTPUT" | grep -E "LINT|WARN|FAIL|error" | head -5
        FAIL=$((FAIL + 1))
      fi
    done
    echo "=== Semantic lint: $PASS pass, $FAIL fail, $SKIP timeout ==="
    [ "$FAIL" -eq 0 ]
