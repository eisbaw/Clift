---
id: TASK-0040
title: 'REVIEW: Pointer and struct semantics correctness'
status: To Do
assignee: []
created_date: '2026-04-08 21:38'
labels:
  - review
  - phase-3
dependencies:
  - TASK-0039
references:
  - ext/tuch-types-bytes-seplogic-popl2007.pdf
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
MPED review of Phase 3a-3b (tasks 0034-0039). Critical: does our memory model faithfully represent C pointer semantics? Are heapUpdate/hVal correct for all byte orders? Are struct layouts ABI-correct? Review against tuch-types-bytes-seplogic-popl2007.pdf.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Memory model reviewed against Tuch's POPL 2007 paper
- [ ] #2 Pointer validity predicate reviewed for completeness
- [ ] #3 Struct layout verified against gcc for all test structs
- [ ] #4 No aliasing-related unsoundness identified
- [ ] #5 Gaps filed as backlog tasks
<!-- AC:END -->
