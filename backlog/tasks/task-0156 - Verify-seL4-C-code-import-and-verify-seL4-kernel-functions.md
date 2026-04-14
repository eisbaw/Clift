---
id: TASK-0156
title: 'Verify seL4 C code: import and verify seL4 kernel functions'
status: Done
assignee: []
created_date: '2026-04-10 18:47'
updated_date: '2026-04-10 23:02'
labels:
  - phase-n
  - industrial
  - seL4
  - milestone
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The ultimate credibility test: verify actual seL4 kernel C code using Clift. The seL4 source (sel4/src/kernel/) contains ~8700 LOC of C. Start with the simplest kernel functions: capability operations (cap_get_capType, cap_get_capPtr), object type checks, simple accessors. These are small, pure-ish functions that exercise bitwise ops and struct access. If Clift can verify seL4's own C, it proves the tool is at the same level as AutoCorres.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 seL4 kernel source obtained (github.com/seL4/seL4)
- [ ] #2 CImporter processes at least 10 seL4 kernel functions
- [ ] #3 clift lifts them to L1
- [ ] #4 At least 5 functions fully verified
- [ ] #5 Comparison: our proof vs AutoCorres2 proof for same function
- [ ] #6 Gap analysis: what seL4 C features does Clift not handle?
<!-- AC:END -->
