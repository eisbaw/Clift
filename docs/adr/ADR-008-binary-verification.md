# ADR-008: Binary Verification Approach

## Status

Accepted (2026-04-08)

## Context

Clift verifies C source code by embedding it into Lean 4 and proving properties.
However, there is a gap between the verified C source and the actual binary that
runs on hardware. The compiler (gcc/clang) could introduce bugs that invalidate
our proofs. This is known as the "compiler trust gap."

seL4 closed this gap for ARM by using translation validation: they compiled with
gcc, decompiled the binary, and proved the decompiled code matches their formal
C model (Section 5 of the TOCS 2014 paper). This took significant effort
(person-years) and was specific to one compiler version and one target architecture.

We need a strategy for Clift. The question: how should Clift handle binary
verification, given our resources and Lean 4 tooling?

## Three Approaches

### Approach 1: Translation Validation

**What**: Compile with any compiler (gcc/clang at a specific -O level), decompile
the binary (objdump/Ghidra/BAP), represent the decompiled code in Lean 4, and
prove it matches the CSimpl embedding.

**seL4's experience**: They used the HOL4 machine-code framework (Myreen) to
decompile ARM binaries into recursive functions, then proved these match the
C-level Simpl semantics. This was done for the entire 9,500-line kernel.

**Feasibility for Clift**:
- Requires: a formal ARM/x86/RISC-V ISA model in Lean 4 (does not exist)
- Requires: a decompilation framework in Lean 4 (does not exist)
- Requires: proof that decompiled code matches CSimpl for every function
- Effort estimate: 2-5 person-years for a single architecture
- The ISA model alone (e.g., ARM Armv8-A) is ~50,000 lines of specification

**Advantages**:
- Works with any compiler at any optimization level
- Catches real compiler bugs (seL4 found none, but the assurance is valuable)
- Architecture-specific: proves the actual binary on the actual hardware

**Disadvantages**:
- Enormous upfront investment in ISA modeling
- Must be redone for each target architecture
- Must be re-validated for each compiler version
- The decompilation tool itself enters the TCB (or must be verified)

### Approach 2: Verified Compiler (CompCert)

**What**: Use CompCert, a formally verified C compiler (proved correct in Coq),
to compile the C code. CompCert guarantees that the compiled binary preserves
the semantics of the C source.

**Feasibility for Clift**:
- CompCert exists and works today
- CompCert's correctness proof is in Coq, not Lean 4
- We would trust CompCert's correctness proof axiomatically
- CompCert supports C99 (with some restrictions), ARM, x86, RISC-V
- CompCert generates less optimized code than gcc -O2 (roughly gcc -O1)

**Advantages**:
- No binary verification needed at all -- the compiler is trusted
- Well-tested, used in production (Airbus, etc.)
- Supports multiple architectures out of the box
- Minimal additional effort for Clift

**Disadvantages**:
- CompCert's proof is in Coq -- we trust it axiomatically from Lean's perspective
- CompCert generates slower code than gcc/clang with optimizations
- CompCert has a restricted C subset (no some GNU extensions)
- CompCert is not free for commercial use (dual license)
- The TCB includes CompCert's unverified parser and assembler
- Cross-prover trust: CompCert's correctness is only as good as Coq's kernel

### Approach 3: Lean-as-Compiler

**What**: Generate code directly from Lean 4, bypassing C entirely. Lean 4 has
a native code generator, and we could in principle emit verified machine code
from the Lean specifications.

**Feasibility for Clift**:
- Lean 4's code generator is NOT verified (it's a practical compiler, not a
  verified one)
- There is no framework for emitting verified machine code from Lean
- The entire Clift architecture assumes C as the source language
- Rewriting Clift to target Lean-native code would be a fundamental redesign

**Advantages**:
- Would eliminate both the compiler trust gap AND the C importer trust gap
- Lean's type system provides stronger guarantees than C

**Disadvantages**:
- Not feasible with current Lean 4 infrastructure
- Would require a verified code generator for Lean (multi-year research project)
- Abandons the goal of verifying EXISTING C code
- Not applicable to embedded/kernel code that must be C

## Prototype Assessment

To ground this decision, I assessed what a minimal binary verification prototype
would look like:

1. **Compile one function** (e.g., `uint32_t max(uint32_t a, uint32_t b)`)
   with `gcc -O0 -o max.o max.c`

2. **Decompile** with `objdump -d max.o` to get the assembly

3. **Manually represent** the assembly as a Lean 4 function

4. **Prove equivalence** between the assembly-level function and the CSimpl term

**Assessment**: Even for this trivial function, step 3 requires:
- A formal model of the target ISA (at minimum: registers, flags, memory)
- A formal model of the calling convention (where are arguments? return value?)
- Instruction semantics for every instruction in the compiled output

For `max` compiled with gcc -O0 on x86-64, the output is approximately 15
instructions including stack frame setup, register moves, comparison, and
conditional move. Formally modeling these 15 instructions requires:
- x86-64 register model (at least RAX, RBX, RDI, RSI, RSP, RBP, EFLAGS)
- Memory model (stack frames, alignment)
- Semantics for: push, mov, cmp, jge/jle, pop, ret

This is doable for one function but does not scale without a complete ISA model.

## Decision

**Primary recommendation: CompCert (Approach 2)**

For practical Clift deployments, use CompCert as the compiler. This eliminates
the compiler trust gap with minimal effort. The cross-prover trust (Coq -> Lean)
is acceptable because:
1. CompCert's proof has been extensively reviewed and tested
2. Both Coq and Lean 4 have small, well-audited kernels
3. The practical risk of a CompCert-specific bug that affects Clift is very low

**Secondary recommendation: Translation validation (Approach 1) for high-assurance**

For systems requiring the highest assurance (e.g., CC EAL7, safety-critical),
invest in translation validation. This should be:
1. Scoped to one architecture (ARM or RISC-V, not x86 initially)
2. Based on an existing ISA model (port from HOL4 or Coq if possible)
3. Targeted at gcc -O0 or -O1 initially (simpler optimizations to validate)

**Not recommended: Lean-as-compiler (Approach 3)**

Not feasible with current infrastructure. Revisit if Lean 4 develops a verified
code generation path.

## Trust Model After Binary Verification

### With CompCert (recommended)
TCB includes:
- Lean 4 kernel (type checker)
- Clift CImporter (C -> CSimpl translation)
- CompCert's unverified components (parser, assembler, linker)
- Hardware

Does NOT include:
- CompCert's compiler passes (verified in Coq)
- gcc/clang (not used)

### With Translation Validation
TCB includes:
- Lean 4 kernel
- Clift CImporter
- ISA model (must be independently validated)
- Decompilation tool (if not verified)
- Hardware

Does NOT include:
- The compiler (any compiler can be used)
- The compiled binary's semantic correctness (proven, not trusted)

### Current (no binary verification)
TCB includes:
- Lean 4 kernel
- Clift CImporter
- The C compiler (gcc/clang)
- Hardware

## Consequences

1. Clift users should be aware that proofs apply to the C source, not the binary,
   unless CompCert is used
2. Documentation should clearly state the trust model
3. The CImporter remains in the TCB regardless of binary verification approach
4. Future work on ISA models in Lean 4 could enable translation validation

## References

- seL4 TOCS 2014, Section 5: "Binary Verification"
- Myreen, "Verified Just-In-Time Compiler on x86" (HOL4 machine-code framework)
- Leroy, "Formal Verification of a Realistic Compiler" (CompCert)
- Kumar et al., "CakeML: A Verified Implementation of ML" (verified compilation in HOL4)
