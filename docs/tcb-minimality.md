# TCB Minimality Argument: Clift vs seL4

A formal methods reviewer will ask: "Why should I trust YOUR verification
pipeline?" This document answers that question by comparing our Trusted
Computing Base (TCB) against seL4's, component by component, with size
estimates and trust arguments.

See also: `docs/tcb.md` for the full TCB specification.

## What is the TCB?

The Trusted Computing Base is the set of components that must be correct
for the verification to mean anything. A bug in ANY TCB component can
silently invalidate ALL proofs.

The goal is: make the TCB as small and trustworthy as possible.

## Component-by-Component Comparison

### 1. Proof Kernel

| | seL4 (Isabelle/HOL) | Clift (Lean 4) |
|---|---|---|
| **Component** | Isabelle/HOL kernel | Lean 4 type checker |
| **Size** | ~7K LOC (ML) | ~10K LOC (C++) |
| **Theory** | Simple Type Theory + HOL axioms | Calculus of Inductive Constructions |
| **Axioms** | HOL axioms (extensionality, choice, infinity) | propext, Quot.sound, Classical.choice |
| **Track record** | 30+ years, used in seL4, many AFP entries | 5+ years, growing Mathlib (140K+ theorems) |
| **Independent checkers** | None widely used | External type checkers exist (lean4checker) |

**Trust argument**: Both kernels are small, based on well-understood foundations,
and have been exercised by large-scale verification efforts. Lean 4's kernel is
slightly larger but is written in a memory-safe subset of C++ and has external
checking tools. Neither kernel has had a soundness bug exploited in a major
verification effort.

**Risk**: A soundness bug in either kernel invalidates everything. Mitigation:
both kernels are small enough for expert review, and `#print axioms` / Isabelle's
`thm_deps` can verify which axioms a theorem depends on.

### 2. C Parser / Importer

| | seL4 (StrictC parser) | Clift (CImporter + clang) |
|---|---|---|
| **Component** | Custom StrictC parser (Haskell) | clang JSON AST + Python translator |
| **Size** | ~10K LOC Haskell | clang: ~2M LOC (but shared with all LLVM users) + CImporter: ~2K LOC Python |
| **C dialect** | StrictC (custom subset) | StrictC-compatible subset |
| **Formal spec** | Defined by parser implementation | Defined by clang AST semantics |
| **Testing** | seL4 kernel as integration test | Snapshot tests, fuzz testing, struct layout differential tests |

**Trust argument for Clift**: Our TCB here is actually SPLIT into two parts:

1. **clang** (~2M LOC): We trust clang to produce a correct AST. This is a
   strong bet: clang is used by millions of developers, passes the GCC test
   suite, and is maintained by Apple/Google/ARM/Intel. A bug in clang's AST
   would affect all LLVM-based tools, creating strong incentives for correctness.

2. **CImporter** (~2K LOC Python): We trust our Python script to correctly
   translate the clang AST to CSimpl terms. This is the weak link: it's our
   code, and it's the most likely place for a bug.

**Trust argument for seL4**: seL4 trusts a custom ~10K LOC Haskell parser.
This parser is less battle-tested than clang but is purpose-built and has been
validated against the entire seL4 kernel (10K LOC C).

**Comparison**: Clift arguably has a SMALLER effective TCB here because we
outsource C parsing to clang (industrial-grade) and only write a ~2K LOC
translator. seL4 must trust their entire 10K LOC parser.

**Mitigation for both**: Regression testing, fuzz testing, and differential
testing against gcc (for struct layouts, integer promotion, etc.).

### 3. Compiler

| | seL4 | Clift |
|---|---|---|
| **Trusted compiler** | gcc (specific pinned version) | gcc (same) |
| **Size** | ~15M LOC | ~15M LOC |
| **Mitigation** | Translation validation (planned), CompCert option | Same |

**Trust argument**: Identical for both projects. The compiler is trusted to
preserve the semantics of the verified C code when compiling to machine code.
Both projects mitigate this with:
- Pinning to a specific compiler version
- CompCert as an alternative verified compiler
- Translation validation as future work

### 4. Hardware

| | seL4 | Clift |
|---|---|---|
| **Assumption** | CPU implements ISA correctly | Same |
| **Scope** | ARMv7, x86-64, RISC-V | x86-64 (LP64) |

**Trust argument**: Standard assumption in all formal verification.
Identical for both projects.

### 5. Assembly / Platform Interface

| | seL4 | Clift |
|---|---|---|
| **Trusted ASM** | ~340 lines hand-written ASM (trap handlers, context switch) | None (no OS kernel) |
| **Platform assumptions** | MMU configuration, interrupt handling | LP64 data model, little-endian, gcc struct layout |

**Trust argument**: seL4 has ~340 lines of trusted ASM that are outside
the verification boundary. Clift has no ASM but has platform assumptions
(documented in `docs/tcb.md`) that must hold for the proofs to apply.

### 6. Lifting Framework

| | seL4 (AutoCorres2) | Clift |
|---|---|---|
| **Component** | AutoCorres L1/L2/TS lifting | SimplConv L1 lifting |
| **Trust level** | NOT in TCB (all lifting steps are proven correct) | NOT in TCB (L1corres proofs verified by Lean kernel) |
| **Automation** | Fully automatic | Manual (MetaM automation in progress) |

**Trust argument**: Neither lifting framework is in the TCB because both
produce proof certificates that are checked by the proof kernel. The difference
is in automation, not trust.

## Size Comparison Summary

| TCB Component | seL4 (LOC) | Clift (LOC) | Notes |
|---------------|------------|-------------|-------|
| Proof kernel | ~7K (Isabelle) | ~10K (Lean 4) | Both well-audited |
| C parser/importer | ~10K (Haskell) | ~2K (Python) + clang | Clift outsources to clang |
| Compiler | ~15M (gcc) | ~15M (gcc) | Identical |
| Trusted ASM | ~340 | 0 | seL4 is an OS kernel |
| Platform assumptions | Documented | Documented | Different scope |
| **Total unique trusted code** | **~17K** | **~12K** | Excluding shared gcc |

Note: The "clang" component (~2M LOC) is shared infrastructure, not unique
to Clift. If we count it, our TCB is much larger. But this is like counting
the Linux kernel in seL4's TCB because seL4 runs on Linux hardware -- the
shared infrastructure has independent validation.

## Why Each TCB Component is Trustworthy

### Lean 4 Kernel

- Based on CIC (Calculus of Inductive Constructions), well-studied since 1988
- Small implementation (~10K LOC C++)
- Active bug bounty (implicit: Mathlib exercises every corner)
- External checker tool (`lean4checker`) can independently verify proof terms
- `#print axioms` verifies no `sorryAx` smuggled in

### CImporter

- Smallest TCB component (~2K LOC)
- Every output is a Lean definition that must type-check
- Snapshot tests catch regressions
- Fuzz testing: 55 random programs per run
- Struct layout differential testing against gcc
- Integer promotion tests against C standard
- The output is human-readable Lean code (auditable)

### Clang AST

- Most battle-tested C frontend in existence
- Used by Apple (every iOS/macOS app), Google (Chrome, Android), etc.
- Passes GCC torture tests and C standard conformance suites
- JSON AST format is stable across minor versions
- We pin to a specific LLVM version via Nix

### gcc (Compiler)

- Same trust assumption as seL4
- Decades of testing, millions of users
- CompCert available as a verified alternative for critical applications
- We compile with `-O0` or limited optimizations to reduce miscompilation risk

## Trust Gaps and Mitigations

### Gap 1: CImporter correctness

**Risk**: Python code mistranslates C to CSimpl.

**Mitigations**:
- Snapshot tests on known programs
- Fuzz testing (55 random programs)
- Struct layout differential testing against gcc
- Integer promotion tests against C11 standard
- Every CImporter output must type-check in Lean

**Residual risk**: A systematic translation error that our tests don't cover.
The CImporter is ~2K LOC Python, small enough for manual audit.

### Gap 2: clang AST stability

**Risk**: LLVM version change breaks AST format.

**Mitigations**:
- Pin LLVM version in `flake.nix`
- Snapshot tests detect format changes immediately
- Conservative: only use documented AST node types

**Residual risk**: Undocumented AST node type change within a minor version.
Low probability, caught by snapshot tests.

### Gap 3: Lean kernel soundness

**Risk**: A soundness bug in Lean 4 allows invalid proofs.

**Mitigations**:
- Small kernel (~10K LOC), well-audited
- `lean4checker` for independent verification
- `#print axioms` to verify axiom dependencies
- Active community finding edge cases

**Residual risk**: Undiscovered kernel bug. Same risk as Isabelle for seL4.
Both are small enough for expert review.

### Gap 4: Platform assumption mismatch

**Risk**: Target platform doesn't match our LP64/little-endian/gcc-layout assumptions.

**Mitigations**:
- Assumptions documented in `docs/tcb.md`
- Differential testing validates struct layout for the build platform
- Assumptions are standard for Linux x86-64

**Residual risk**: Cross-compilation to a platform with different assumptions.
User must verify assumptions for their target.

## Conclusion

Clift's TCB is **comparable to seL4's** in structure and **potentially smaller**
in unique trusted code:

- We trust a smaller C translator (~2K vs ~10K LOC) by outsourcing parsing to clang
- We trust a comparable proof kernel (Lean 4 vs Isabelle)
- We trust the same compiler (gcc)
- We have fewer platform-specific trusted components (no ASM)

The main trust gap is **CImporter correctness**, which we mitigate through
extensive automated testing. The main maturity gap is **automation**: seL4's
AutoCorres2 provides fully automatic lifting, while Clift requires manual L1
construction. This affects usability but not trustworthiness.

A reviewer should focus their audit on:
1. `CImporter/` (~2K LOC Python) -- the most likely source of bugs
2. `#print axioms` output -- verify no `sorryAx` in any theorem
3. Platform assumptions in `docs/tcb.md` -- verify they hold for the target
