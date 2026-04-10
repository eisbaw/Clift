# External Review Plan

## Purpose

Independent review of Clift's proof infrastructure by a formal methods expert to identify unsound assumptions, missed edge cases, and architectural weaknesses before relying on Clift for real verification work.

## What We Would Ask a Reviewer to Check

### 1. Soundness of the Refinement Chain
- Does the `corres` definition correctly capture backward simulation?
- Does transitivity of `corres` hold (are the composed refinement proofs valid)?
- Are there any axioms or assumptions that break soundness?
- Review `Examples/AxiomAudit.lean` for the current axiom inventory

### 2. Trust Boundary (CImporter)
- Does the CImporter correctly translate C semantics for the supported subset?
- Are there C constructs where the translation silently diverges from C11/C17?
- Integer promotion, implicit conversions, undefined behavior guards
- Review `docs/int-promotion-audit.md` and `docs/tcb.md` for known issues

### 3. Memory Model Correctness
- Does `HeapRawState` correctly model C's memory semantics?
- Struct padding, alignment, byte order assumptions
- Pointer validity and aliasing rules
- Does `simpleLift` correctly abstract raw bytes to typed values?

### 4. Security Property Meaningfulness
- Do the integrity/confidentiality/availability definitions capture real security properties?
- Is the noninterference formulation sound (step consistency + locally respects)?
- Does the refinement transfer theorem actually propagate security to C?
- Are the capability/authority confinement patterns correct?

### 5. Exec Semantics
- Does the big-step `Exec` relation correctly model C execution?
- Are all CSimpl constructors covered with correct rules?
- Does the partial correctness interpretation (no derivation = non-termination) match intent?
- Review `Examples/ExecAudit.lean` for the current assessment

### 6. Lean 4 Proof Quality
- Are proofs robust or do they rely on fragile tactics that might break?
- Are there proofs that are correct but not for the intended reason (proving False, vacuous truth)?
- Review `Examples/SorryAudit.lean` for remaining proof gaps

## Artifacts to Provide

1. **Repository access**: full Git history, all source files
2. **Build instructions**: `nix develop` + `lake build` (reproducible via flake.nix)
3. **Documentation**: plan.md (architecture), docs/ directory, CLAUDE.md
4. **Key files to start with**:
   - `Clift/MonadLib/Corres.lean` (refinement definition)
   - `Clift/CSemantics/Exec.lean` (operational semantics)
   - `Clift/CSemantics/HeapRaw.lean` (memory model)
   - `Clift/Security/Properties.lean` (security framework)
   - `CImporter/import.py` (trust boundary)
5. **Test suite**: `test/` directory, `Justfile` for running tests
6. **Known limitations**: `docs/tcb.md`, audit lean files in Examples/

## Suggested Reviewers

### Primary Targets (Lean 4 + formal verification)
- **Leonardo de Moura's group** (Lean FRO): deep Lean 4 expertise
- **Jasmin Blanchette** (LMU Munich): Lean 4 formalization, Mathlib contributor
- **Jeremy Avigad** (CMU): Lean 4, mathematical formalization

### Secondary Targets (C verification + Isabelle/HOL)
- **Gerwin Klein** (Proofcraft/UNSW): seL4 lead, could assess AutoCorres fidelity
- **David Greenaway**: AutoCorres author, could assess architectural choices
- **Robbert Krebbers** (Radboud): Iris/RefinedC, could compare approaches

### Tertiary Targets (formal methods, general)
- **Xavier Leroy** (INRIA/College de France): CompCert, could assess C semantics
- **Adam Chlipala** (MIT): Coq verification, could assess methodology
- **Derek Dreyer** (MPI-SWS): RustBelt/Iris, could assess separation logic approach

## Review Process

### Phase 1: Self-Assessment (1 week)
- Run all audit files, document remaining issues
- Ensure build is clean (no warnings, no sorry in library code)
- Write a reviewer guide document

### Phase 2: Initial Review (2-3 weeks)
- Reviewer examines documentation and key files
- Reviewer tries to build the project and run tests
- Reviewer writes initial findings

### Phase 3: Adversarial Testing (1-2 weeks)
- Reviewer attempts to prove False using the framework
- Reviewer attempts to verify an incorrect C program
- Reviewer checks if axioms can be exploited

### Phase 4: Report and Response (2 weeks)
- Reviewer delivers written report
- We address critical findings
- Iterate if needed

## Expected Timeline

- **Preparation**: 1-2 weeks (clean up, write reviewer guide)
- **Review engagement**: 1-2 weeks (find reviewer, negotiate terms)
- **Active review**: 3-5 weeks
- **Response and fixes**: 2-4 weeks
- **Total**: 2-3 months

## Budget Considerations

- Academic reviewers: may do it for co-authorship or acknowledgment
- Industry reviewers (Proofcraft, Galois): likely paid engagement, estimate $5K-$15K
- Student reviewers: lower cost but may miss subtle issues
- Recommendation: prioritize one senior reviewer over multiple junior ones
