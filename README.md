# Clift: Lifting C into Lean 4 for Formal Verification

Clift verifies imperative C code by lifting it into Lean 4 — the same methodology seL4's AutoCorres uses in Isabelle/HOL, brought to the Lean 4 ecosystem for AI-assisted proof automation.

## What it does

```
C source (.c)
    |  clang -ast-dump=json
    v
CImporter (Python)        Parses C, emits Lean 4 CSimpl terms
    |
    v
clift (Lean 4 command)    Lifts through 5 abstraction stages:
    |                      L1: CSimpl -> NondetM monad
    |                      L2: Extract locals to lambda params
    |                      L3: Narrow monad (pure/option/nondet)
    |                      L4: Typed heaps (simpleLift)
    |                      L5: BitVec -> Int/Nat
    v
User proofs               Properties that chain back to actual C
```

Every proof is checked by the Lean 4 kernel. The proofs apply to the **actual C code**, not a rewrite or model.

## Status

- **55K+ LOC** (Lean 42K + Python 4.4K + C tests 4.4K + docs 2.4K)
- **260 C functions** across 13 verification domains
- **Zero sorry in core library** (Clift/)
- **27 sorry remaining** in example proofs (down from 65, actively being eliminated)
- **215+ backlog tasks done**
- **Soundness tested**: attempted to prove False, all attempts failed

## Verified examples

| Domain | C LOC | Functions | Highlights |
|--------|-------|-----------|------------|
| Ring buffer | 676 | 40 | Abstract FIFO spec, invariant preservation, security property |
| RTOS queue | 290 | 24 | Priority-based insertion, ISR-safe ops |
| SHA-256 core | 230 | 14 | FIPS 180-4 building blocks, constant-time |
| UART driver | 280 | 15 | MMIO register manipulation, state machine |
| Packet parser | 340 | 14 | Ethernet + IPv4 with bounds checking |
| seL4 capabilities | ~100 | 6 | Bitfield extraction, all classified PURE |
| Hash table | ~200 | 7 | Open addressing, linear probing |
| Memory allocator | ~200 | 6 | First-fit, free list |
| Red-black tree | ~200 | 7 | Insert, lookup, rotate |
| State machine | ~150 | 9 | TCP-like connection states |
| Priority queue | ~150 | 10 | Binary heap |
| DMA buffer | ~200 | 10 | Circular hardware buffer |
| Multi-call | ~100 | 5 | Inter-procedural verification |

## Key proofs

- **gcd_correct_nat**: C `gcd()` computes GCD over natural numbers (full pipeline, zero sorry)
- **swap_correct**: Pointer exchange with heap reasoning (zero sorry)
- **rbt_lookup_correct**: Red-black tree BST search through L1_hoare_while (zero sorry)
- **rb_push/rb_find_index**: Ring buffer linked-list mutation and traversal with loop invariants
- **uart_init**: 11-field struct initialization with chained heapUpdate (zero sorry)
- **ring_buffer_ext refinement**: Abstract FIFO queue spec refines to C (21/40 functions proven)
- **Partition isolation**: Security property for two-partition ring buffer

## Architecture

```
Clift/
  MonadLib/       NondetM, Hoare triples, corres (backward simulation)
  CSemantics/     CSimpl, Exec (22 rules), Terminates, State, Concurrency, MultiArch
  Lifting/        L1-L5 stages, FuncSpec, AbstractSpec, GlobalInvariant, WP calculus
  Security/       Integrity, Confidentiality, Noninterference, Capabilities, PageTable, ...
  Tactics/        c_step, c_vcg, sep_auto, corres_auto, l1_vcg
  AI/             InvariantGen, SpecGen, ProofIndex
  Specs/          Reusable: Queue, Stack, StateMachine, Counter, RingBuffer, BoundedMap
  Util/           SetBasic, UInt extensions

CImporter/        Python: clang JSON AST -> Lean 4 CSimpl
Generated/        CImporter output (version controlled)
Examples/         Verification proofs
```

## Quick start

```bash
nix develop          # Enter nix environment
lake build           # Build everything
just import test/c_sources/gcd.c Gcd   # Import a C file
just e2e             # Run end-to-end tests
just regression      # Run full regression suite
just lint            # Check for sorry + tautological postconditions
just sorry-count     # Quick sorry audit
```

See [docs/user-guide.md](docs/user-guide.md) for the full walkthrough.

## Supported C subset (StrictC)

Arithmetic, pointers, structs, arrays, enums, typedefs, globals, function calls, bitwise ops, type casts, sizeof, for/do-while/switch, multi-file, unions, void*, char. No floating point, goto, address-of locals, inline assembly (axiomatized), or VLAs.

## Design decisions

8 ADRs in [backlog/docs/](backlog/docs/) covering: L1 exception encoding, Mathlib removal, while semantics, address space, stuck/fault merge, guard parameters, address-of locals, binary verification.

## Trust model

**Trusted** (in TCB): Lean 4 kernel, CImporter, clang, C compiler, hardware.
**Proven** (not trusted): Everything in Clift/ — monadic lifting, Hoare rules, corres, security properties.

See [docs/tcb.md](docs/tcb.md) for the full analysis.

## License

BSD-2-Clause. See [LICENSE](LICENSE).
