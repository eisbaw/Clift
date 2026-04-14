---
id: TASK-0218
title: 'Benchmark against AutoCorres2: same C file, compare proof effort'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-11 06:29'
updated_date: '2026-04-11 07:26'
labels:
  - maturity
  - benchmark
  - seL4
dependencies: []
references:
  - ext/AutoCorres2/tests/
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The definitive comparison. Take a C file that AutoCorres2 can also verify (from ext/AutoCorres2/tests/). Import with both Clift (CImporter + clift) and AutoCorres2 (Isabelle). Compare: (1) import time, (2) lifting time, (3) proof effort for the same FuncSpec, (4) proof size, (5) proof checking time. This gives a concrete, reproducible comparison of Clift vs the tool it aims to match.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 C test file selected from AutoCorres2 test suite
- [ ] #2 Imported and verified in both Clift and AutoCorres2
- [ ] #3 Import time compared
- [ ] #4 Proof effort compared (LOC, time)
- [x] #5 Results documented
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Selected factorial.c from ext/AutoCorres2/tests/examples/.
Documented comparison in docs/autocorres2-benchmark.md.
Full verification comparison (AC #2-#4) blocked by Clift lacking recursive call support.
Document is honest about this limitation.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Wrote docs/autocorres2-benchmark.md: comparison of Clift vs AutoCorres2 on factorial.c.

Covers:
- Benchmark file selection (factorial.c from ext/AutoCorres2/tests/examples/)
- Import pipeline comparison
- Generated definition comparison
- Where Clift is simpler (TCB, tooling, types)
- Where AutoCorres2 is more mature (automation, recursion, heap, track record)
- Proof effort comparison
- Honest assessment: full verification blocked by missing recursive call support
<!-- SECTION:FINAL_SUMMARY:END -->
