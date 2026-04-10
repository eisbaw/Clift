# Attribution

Clift builds on foundational work from the formal verification community. This file acknowledges the projects, papers, and people whose work Clift depends on or draws from.

## AutoCorres2 (Primary Influence)

Clift's architecture is a Lean 4 adaptation of the AutoCorres pipeline, originally developed for Isabelle/HOL.

**AutoCorres2** is the modernized version of AutoCorres in the Archive of Formal Proofs.

- **Authors**: David Greenaway, Japheth Lim, Gerwin Klein, Fabian Hölzl, Fabian Immler, Norbert Schirmer, Lars Hupel, Daniel Matichuk, Thomas Sewell, Matthew Brecknell
- **License**: BSD (code), CC-BY-SA-4.0 (documentation)
- **Source**: https://www.isa-afp.org/entries/AutoCorres2.html
- **Paper**: David Greenaway, Japheth Lim, June Andronick, Gerwin Klein. "Don't Sweat the Small Stuff: Formal Verification of C Code Without the Pain." PLDI 2014.

See `ext/AutoCorres2/README.md` for the full author list and detailed per-file attribution.

## Simpl (Schirmer)

CSimpl, Clift's deeply embedded imperative language, is based on Simpl.

- **Author**: Norbert Schirmer
- **Paper**: "Verification of Sequential Imperative Programs in Isabelle/HOL." PhD thesis, TU München, 2006.
- **License**: BSD (as part of AFP)

## seL4

The verification methodology (refinement-based, security properties via transfer theorems) follows seL4's approach.

- **Authors**: Gerwin Klein, June Andronick, Kevin Elphinstone, Gernot Heiser, David Cock, Philip Derrin, Dhammika Elkaduwe, Kai Engelhardt, Rafal Kolanski, Michael Norrish, Thomas Sewell, Harvey Tuch, Simon Winwood
- **Paper**: Gerwin Klein et al. "Comprehensive Formal Verification of an OS Kernel." ACM TOCS, 2014.
- **Paper**: Gerwin Klein et al. "seL4: Formal Verification of an OS Kernel." SOSP 2009.
- **License**: GPL-2.0 (kernel), BSD (proofs)
- **Source**: https://github.com/seL4

## Lean 4

Clift is implemented in Lean 4.

- **Authors**: Leonardo de Moura, Sebastian Ullrich, and the Lean community
- **License**: Apache-2.0
- **Source**: https://github.com/leanprover/lean4

## Memory Model

The memory model (Types, Bytes, and Separation Logic) is influenced by:

- **Author**: Harvey Tuch
- **Paper**: Harvey Tuch, Gerwin Klein, Michael Norrish. "Types, Bytes, and Separation Logic." POPL 2007.

## Other Influences

- **Aeneas** (Son Ho, Jonathan Protzenko): Rust-to-Lean verification, progress/step tactic patterns
- **CompCert** (Xavier Leroy et al.): C semantics reference (Clight)
- **Mathlib** (the Lean community): Mathematical foundations, tactic library
- **lean-mlir/SSA**: Denotational semantics patterns

## License Terms Summary

| Component | License |
|-----------|---------|
| Clift (this project) | BSD-2-Clause |
| AutoCorres2 code | BSD |
| AutoCorres2 docs | CC-BY-SA-4.0 |
| seL4 proofs | BSD |
| Lean 4 | Apache-2.0 |

## Note

This project does not include copies of the above projects' code (except for reference material in `ext/`). Clift is an independent implementation in Lean 4, inspired by the architectural ideas and verification methodology of AutoCorres/seL4.
