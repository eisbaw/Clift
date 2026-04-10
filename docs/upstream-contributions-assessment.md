# Upstream Contributions Assessment: CImporter vs AutoCorres2 C Parser

## Purpose

Document where Clift's CImporter differs from AutoCorres2's C parser (StrictC/SML-based), identify potential contributions to the Isabelle community, and assess feasibility.

## CImporter Architecture

Clift's CImporter is a Python script that reads `clang -Xclang -ast-dump=json` output and emits Lean 4 `.lean` files containing CSimpl terms. This is fundamentally different from AutoCorres2's approach:

| Aspect | AutoCorres2 (StrictC) | Clift (CImporter) |
|--------|----------------------|-------------------|
| Language | SML (within Isabelle) | Python |
| Input | C source directly (custom parser) | clang JSON AST |
| Output | Isabelle/HOL terms | Lean 4 terms |
| Preprocessing | Limited (own preprocessor) | Full (clang handles it) |
| Trust model | Parser is in TCB | clang + importer in TCB |

## CImporter Capabilities vs StrictC

### Features CImporter handles that StrictC does/did not

1. **Post-increment/decrement in expressions**: CImporter decomposes `a++` into a read + increment sequence. AutoCorres2 added similar support in Feb 2025 (after our implementation).

2. **Flexible array members**: CImporter handles `struct { int n; int data[]; }` by modeling the flexible member as a pointer with bounds. StrictC historically rejected these.

3. **Anonymous structs/unions**: CImporter handles `struct { struct { int x; }; }` by flattening fields. StrictC requires named members.

4. **Enum with explicit values**: CImporter handles `enum { A = 5, B = 10 }` with arbitrary integer values. StrictC treats enums as simple sequential integers.

5. **Typedef chains**: CImporter resolves typedef chains (`typedef uint32_t mytype; typedef mytype othertype;`) to base types. StrictC handles simple typedefs but complex chains can fail.

6. **Multi-file projects**: CImporter can process multiple .c files with shared headers, generating a coherent set of Lean definitions. StrictC operates on single translation units.

7. **C11 atomics (partial)**: CImporter recognizes `_Atomic` qualifiers and generates appropriate annotations, though verification of atomic semantics is not yet implemented.

### Features StrictC handles that CImporter does not

1. **Goto statements**: StrictC can handle limited goto patterns. CImporter rejects all goto.

2. **Bitfield structs**: StrictC models C bitfields. CImporter does not support them yet.

3. **Inline assembly**: StrictC has limited support. CImporter rejects all inline assembly.

4. **CompCert-validated semantics**: StrictC's semantics have been cross-validated against CompCert's Clight. CImporter relies on clang, which is not formally verified.

## Potential Contributions

### 1. Clang JSON AST as alternative front-end (Low feasibility)
- AutoCorres2 is deeply tied to its SML parser within Isabelle
- Replacing it with clang JSON would require rewriting the entire front-end
- However, a clang-based validator that checks StrictC output against clang's AST could be valuable as a differential testing tool
- **Recommendation**: Offer as a testing/validation tool, not a replacement

### 2. Multi-file processing patterns (Medium feasibility)
- Our approach to handling cross-file dependencies (shared type definitions, extern declarations) could be adapted
- AutoCorres2 currently processes one file at a time
- **Recommendation**: Document our approach, offer as a design reference

### 3. Test cases for edge cases (High feasibility)
- Our test suite includes edge cases (integer promotion, implicit conversions, signed overflow) that could augment AutoCorres2's test suite
- These are language-independent -- the expected C semantics are the same
- **Recommendation**: Contribute test cases with expected behavior documentation

### 4. Post-increment decomposition technique (Already done upstream)
- AutoCorres2 added this in Feb 2025
- Our approach is similar but implemented differently
- **Recommendation**: No action needed, but compare implementations for correctness

### 5. Anonymous struct flattening (Medium feasibility)
- Our field-flattening approach could be adapted to SML
- Relevant for verifying real-world C code that uses anonymous structs
- **Recommendation**: Write up the approach, offer to AutoCorres2 maintainers

## Assessment Summary

The most practical contribution is **test cases** (item 3): these are immediately useful, require no code porting, and help both communities. The clang-based differential testing tool (item 1) could also be valuable but requires more work to make it useful to the Isabelle community.

Direct code contributions are limited by the fundamental architecture difference (Python + clang JSON vs SML + custom parser). The value flow is more likely to be ideas and techniques rather than code.

## Contacts

- AutoCorres2 maintainers: Matthew Brecknell, Gerwin Klein (Proofcraft)
- AutoCorres2 repository: https://www.isa-afp.org/entries/AutoCorres2.html
- seL4 verification team: https://proofcraft.systems/
