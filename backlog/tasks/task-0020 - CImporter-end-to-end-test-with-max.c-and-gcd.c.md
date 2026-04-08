---
id: TASK-0020
title: 'CImporter: end-to-end test with max.c and gcd.c'
status: Done
assignee:
  - '@mped'
created_date: '2026-04-08 21:35'
updated_date: '2026-04-08 23:19'
labels:
  - phase-1
  - cimporter
  - test
dependencies:
  - TASK-0019
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Run CImporter on test/c_sources/max.c and gcd.c. Verify generated .lean files compile. Create snapshot tests in test/expected/. Verify just import and just test-snapshots work.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 just import test/c_sources/max.c Max succeeds
- [x] #2 just import test/c_sources/gcd.c Gcd succeeds
- [x] #3 Generated/Max.lean compiles with lake build
- [x] #4 Generated/Gcd.lean compiles with lake build
- [x] #5 Snapshot tests created and just test-snapshots passes
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
All e2e tests pass:
- just import works for both max.c and gcd.c
- lake build Generated succeeds (Max 235ms, Gcd 250ms)
- Snapshot tests in test/expected/ match generated output
- just e2e runs full pipeline: pytest -> snapshots -> lake build
- Updated lakefile.lean to use roots instead of srcDir for Generated
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
End-to-end CImporter pipeline verified.

Pipeline: clang -ast-dump=json -> CImporter/import.py -> Generated/*.lean -> lake build
Both max.c and gcd.c generate compilable Lean 4 CSimpl definitions.
Snapshot tests ensure output stability.
just e2e runs the full verification: pytest + snapshots + lake build.
<!-- SECTION:FINAL_SUMMARY:END -->
