---
id: TASK-0218
title: 'Benchmark against AutoCorres2: same C file, compare proof effort'
status: To Do
assignee: []
created_date: '2026-04-11 06:29'
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
- [ ] #1 C test file selected from AutoCorres2 test suite
- [ ] #2 Imported and verified in both Clift and AutoCorres2
- [ ] #3 Import time compared
- [ ] #4 Proof effort compared (LOC, time)
- [ ] #5 Results documented
<!-- AC:END -->
