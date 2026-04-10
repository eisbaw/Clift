# Trusted Computing Base (TCB) for Clift

Task 0184: Complete formal TCB specification.

This document specifies exactly what is trusted, what is proven, and what
assumptions the Clift verification pipeline makes. A formal methods expert
should be able to review this single document to understand the assurance
argument.

## What is the TCB?

The Trusted Computing Base is the set of components that must be correct
for the verification to be meaningful. A bug in any TCB component could
silently invalidate all proofs.

## TCB Components

### 1. Lean 4 Kernel

**What**: The Lean 4 type checker and kernel that validates proof terms.

**Trust level**: HIGH. This is the ultimate arbiter of proof validity.
If the Lean kernel has a soundness bug, proofs may be accepted that are
not actually valid.

**Mitigations**:
- Lean 4 kernel is small (~10K LOC) and well-audited
- Based on the Calculus of Inductive Constructions (well-understood theory)
- Active community finding and fixing kernel bugs
- `#print axioms` verifies which axioms a theorem depends on

**Lean axioms used** (from AxiomAudit.lean):
- `propext` (propositional extensionality): standard, used by all Lean math
- `Quot.sound` (quotient soundness): standard, rarely used directly
- `Classical.choice` (axiom of choice): used via `Classical.em` for case splits
- `sorryAx` **must NOT appear** in final verified theorems

### 2. CImporter (Python)

**What**: Python script that reads clang JSON AST and emits .lean files
containing CSimpl terms, state records, and type instances.

**Files**: `CImporter/ast_parser.py`, `CImporter/lean_emitter.py`,
`CImporter/c_types.py`

**Trust level**: HIGH. If the CImporter mistranslates C to CSimpl,
all proofs are about the wrong program and do not apply to the real C code.

**What can go wrong**:
- Incorrect translation of C expressions to CSimpl terms
- Missing UB guards (guard should be present but is not)
- Wrong type mappings (e.g., wrong integer width)
- Missing or incorrect struct layout computation
- Incorrect integer promotion handling

**Mitigations**:
- Regression tests against known C semantics edge cases
  (test/c_sources/edge_cases/)
- Snapshot tests: re-import known programs, diff against expected output
- Struct layout differential testing against gcc (test_struct_layout.py)
- Fuzz testing: random C programs through pipeline (test/fuzz_cimporter.py)
- Integer promotion tests (test/test_int_promotion.py)
- C11 standard coverage documented (docs/c11-coverage.md)

**Known limitations** (documented, not bugs):
- Locals zero-initialized instead of indeterminate (task-0060)
- Globals stored in Locals record (Phase 1 limitation)
- No short-circuit evaluation modeling (mitigated by StrictC no-side-effects rule)
- Shift UB (shift >= width) not guarded

### 3. Clang (AST Dump)

**What**: `clang -Xclang -ast-dump=json` produces the JSON AST that
CImporter consumes.

**Trust level**: MEDIUM. Clang is mature and well-tested, but the JSON
AST format is not formally specified or versioned.

**What can go wrong**:
- Clang AST misrepresents C semantics (e.g., wrong type for an expression)
- JSON format changes between LLVM versions
- Implicit conversions not represented in AST

**Mitigations**:
- Pin to specific LLVM version via nix flake
- Regression tests on known programs detect format changes
- Clang's own extensive test suite validates AST correctness
- We rely on clang's ImplicitCastExpr nodes for integer promotions

### 4. C Compiler (Target)

**What**: The C compiler that compiles the original `.c` file to machine code.

**Trust level**: MEDIUM. Our proofs say "the CSimpl semantics matches the
abstract spec." For this to imply the binary is correct, the compiler must
preserve those semantics.

**What can go wrong**:
- Compiler bug that miscompiles the verified code
- Compiler exploits UB that we model as nondeterministic (but we model as fault)
- Compiler optimizations that assume no UB where our guards guarantee no UB

**Mitigations**:
- StrictC restrictions eliminate many optimization-related UB cases
- All UB in our model produces .fault, so our proofs only hold for
  executions that do NOT trigger UB
- CompCert can be used as a verified compiler for the final binary
- Translation validation (comparing binary against CSimpl) is future work (ADR-008)

### 5. Lean Mathlib / Library Code

**What**: Lean standard library and any Mathlib lemmas used in proofs.

**Trust level**: LOW (these are checked by the Lean kernel). Mathlib
lemmas are themselves proven, so they are NOT in the TCB. The Lean kernel
verifies every lemma we use.

**Exception**: If Mathlib uses `sorry` or `native_decide` unsoundly,
that would be a TCB issue. `#print axioms` detects this.

### 6. Hardware

**What**: The physical machine executing the compiled C code.

**Trust level**: ASSUMED CORRECT. Standard assumption in all formal
verification (including seL4).

**Assumptions**:
- CPU correctly implements the ISA
- Memory is not corrupted by external factors
- No cosmic ray bit flips (or ECC corrects them)

This is identical to seL4's hardware trust assumption.

## What is Proven (NOT in TCB)

The following are verified by the Lean kernel and do NOT need to be trusted:

| Component | What is proven |
|-----------|---------------|
| CSimpl semantics (Exec) | Big-step execution rules are well-formed inductive definitions |
| Hoare logic rules | validHoare/totalHoare rules are sound w.r.t. NondetM semantics |
| corres (refinement) | Backward simulation is transitive, composes correctly |
| L1 lifting (SimplConv) | CSimpl -> NondetM preserves behavior (L1corres theorems) |
| L2 lifting (LocalVarExtract) | Local variable extraction preserves behavior |
| Function specifications | Each FuncSpec.satisfiedBy is a Hoare triple about the L1 body |
| Abstract spec refinement | opRefinement connects L1 bodies to abstract specs |
| Invariant preservation | all_ops_preserve_invariant: every operation maintains the invariant |
| System-level correctness | system_exec_refines: any trace simulates abstract trace |

## What is Assumed (Axioms / Assumptions)

### Lean Axioms
1. **propext**: `(a ↔ b) → a = b` -- standard, non-controversial
2. **Quot.sound**: Quotient types respect equivalence relations -- standard
3. **Classical.choice**: Axiom of choice -- standard for classical math

These are the standard axioms used by all Lean 4 mathematics.
They do NOT weaken the verification in any practical sense.

### Platform Assumptions
1. **Two's complement signed integers**: Universal since C23, and true for
   all platforms since the 1990s.
2. **Little-endian byte order**: True for x86-64. CImporter struct layout
   assumes little-endian.
3. **LP64 data model**: `int` = 32 bits, `long` = 64 bits. True for
   Linux x86-64.
4. **gcc-compatible struct layout**: Padding and alignment follow the
   System V x86-64 ABI. Verified by differential testing (test_struct_layout.py).
5. **char is signed**: True for gcc on x86-64 Linux.

### Semantic Assumptions
1. **No concurrent access**: Our model is sequential. No threads,
   no interrupts accessing shared state.
2. **No hardware faults**: CPU, memory, and I/O work correctly.
3. **No malloc/free**: Heap is static. Dynamic allocation is not modeled.
4. **StrictC compliance**: The C source must comply with StrictC restrictions
   (no goto, no VLAs, no side-effect expressions, etc.).

## Excluded C Features and Why

| Feature | Reason for Exclusion |
|---------|---------------------|
| Floating-point | Phase 1 scope; requires separate verification framework |
| goto / longjmp | Makes control flow analysis intractable; StrictC restriction |
| Switch fall-through | Error-prone; StrictC restriction |
| Address-of locals (&x) | Would require modeling stack as heap; StrictC restriction |
| Side effects in expressions | Makes evaluation order matter; StrictC restriction |
| Variadic functions | Type safety not statically checkable |
| VLAs | Size not statically known; StrictC restriction |
| Pre/post increment in expressions | Side effect; StrictC restriction |
| Function pointers | Future work (Phase 5) |
| Inline assembly | Cannot be verified; trusted if used |
| volatile | Hardware interaction semantics; future work |
| _Atomic / threads | Concurrency; future work (Phase 5) |
| malloc/free | Dynamic allocation; future work |
| Bit-fields | Complex layout rules; future work |
| Complex types | Rarely used in embedded; excluded |

## Threat Model

### What Clift Proofs Prevent

Given a correctly compiled StrictC program where our proofs hold:

1. **Functional incorrectness**: The C code computes the wrong result.
   Our proofs establish that C behavior matches the abstract spec.

2. **Memory safety violations** (within our model):
   - Null pointer dereference: guarded by heapPtrValid
   - Buffer overflow: guarded by heapPtrValid bounds check
   - Type confusion: guarded by TypeTag mismatch detection
   - Unaligned access: guarded by alignment check

3. **Integer overflow (signed)**: Guarded by signed overflow guards.
   Unsigned overflow is well-defined wrapping (not UB).

4. **Division by zero**: Guarded by divisor-nonzero guards.

### What Clift Proofs Do NOT Prevent

1. **Compiler bugs**: If gcc miscompiles the code, the binary may not
   match our proven semantics. Mitigation: use CompCert.

2. **Hardware faults**: Cosmic rays, memory corruption, CPU bugs.
   Standard assumption in all verification.

3. **Concurrency bugs**: Our model is sequential. Data races, deadlocks,
   and atomicity violations are not addressed.

4. **Side-channel attacks**: Timing, power analysis, cache attacks.
   Our model does not reason about execution time or cache state.

5. **CImporter bugs**: A bug in the Python importer could silently
   mistranslate C to CSimpl. Mitigated by extensive testing.

6. **Unsupported C features**: Code using goto, VLAs, or other excluded
   features cannot be verified.

7. **Dynamic allocation bugs**: Use-after-free, double-free, memory leaks.
   Not modeled (no malloc/free).

## Comparison with seL4

| Aspect | seL4 | Clift |
|--------|------|-------|
| Kernel/checker | Isabelle/HOL | Lean 4 |
| C parser trust | StrictC parser (Haskell) | CImporter (Python) + clang |
| C subset | StrictC | StrictC (compatible restrictions) |
| Compiler trust | gcc (with translation validation planned) | gcc (same) |
| Hardware trust | Assumed correct | Assumed correct |
| Concurrency | Single-core (verified) | Sequential only |
| Memory model | UMM (typed heap) | HeapRawState (typed heap, similar to UMM) |
| Separation logic | Yes (split heap) | Phase 3d (basic, no full automation) |
| Scale | ~10K LOC kernel | ~1K LOC (ring buffer) -- scaling up |

## Certification Relevance

For DO-178C (aerospace) or Common Criteria (CC) certification:

- **TCB components** map to certification tool qualification requirements
- **Assumptions** map to Environmental Conditions in the Safety Assessment
- **Proven properties** map to Formal Verification objectives (Table MB.6-6)
- **Excluded features** define the Operational Domain of the verification

A certifier reviewing Clift would need to:
1. Review this TCB document
2. Verify that `#print axioms` shows no `sorryAx` in final theorems
3. Review CImporter test coverage (the main TCB risk)
4. Accept platform assumptions or validate them for the target
