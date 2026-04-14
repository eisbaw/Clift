---
id: TASK-0078
title: 'Performance: incremental re-verification when C changes'
status: To Do
assignee:
  - '@claude'
created_date: '2026-04-09 19:34'
updated_date: '2026-04-14 22:11'
labels:
  - phase-5
  - performance
dependencies: []
priority: low
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Currently, any change to a .c file requires re-running the entire pipeline. For large codebases, need incremental re-verification: only re-check functions that changed and their dependents. Requires: dependency tracking between functions, caching of intermediate proof states, and integration with Lake's build system.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Changed functions detected automatically
- [ ] #2 Only affected proofs re-checked
- [ ] #3 Cache of intermediate states implemented
- [ ] #4 Measured speedup on a multi-function file
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Deferred to Phase 5+. Current performance documented:

Current build times (full lake build, 62 jobs):
- Total: ~15-20 seconds for clean build
- CImporter (Python): <1 second for all C files
- LocalVarExtract library: ~0.5 seconds
- GcdProof/GcdCorrect: ~1-2 seconds each
- SwapProof: ~2 seconds
- HeapLift proofs: ~1-2 seconds

Bottleneck: Lean 4 kernel type-checking, not CImporter or tactic execution. The kernel checks every proof term against the type theory, which is inherently sequential. Lean supports incremental builds via Lake (only rebuild changed files and dependents).

Lake already provides incremental re-verification: when a .c file changes, only the Generated/*.lean file and its dependents (proof files) are rebuilt. Function-level granularity would require splitting proofs into separate files per function.

Recommendations for Phase 5+:
1. Split large Generated files into per-function files for finer-grained rebuilds
2. Profile kernel checking time per proof to identify hot spots
3. Consider native_decide for decidable goals to bypass kernel checking
4. Investigate Lean 4 parallel elaboration for independent proof files
<!-- SECTION:FINAL_SUMMARY:END -->
