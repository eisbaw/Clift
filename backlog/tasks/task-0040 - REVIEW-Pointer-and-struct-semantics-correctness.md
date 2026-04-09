---
id: TASK-0040
title: 'REVIEW: Pointer and struct semantics correctness'
status: Done
assignee:
  - '@mped'
created_date: '2026-04-08 21:38'
updated_date: '2026-04-09 17:13'
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
- [x] #1 Memory model reviewed against Tuch's POPL 2007 paper
- [x] #2 Pointer validity predicate reviewed for completeness
- [x] #3 Struct layout verified against gcc for all test structs
- [x] #4 No aliasing-related unsoundness identified
- [x] #5 Gaps filed as backlog tasks
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Review of Phase 3a-3b pointer and struct semantics against Tuch POPL 2007 and AutoCorres2/TypHeapSimple.thy.

Findings:
1. Our model follows TypHeapSimple (simple lift, whole-struct access only) -- correct design choice
2. heapPtrValid only checks base address htd tag, not full footprint (filed task-0064, HIGH)
3. heapPtrValid missing alignment check (filed task-0065, MEDIUM)
4. No type-safety disjointness theorem (filed task-0066, HIGH, depends on 0064)
5. Struct roundtrip proofs use sorry (filed task-0067, MEDIUM)
6. Missing MemType surjection property (filed task-0068, LOW)
7. 32-bit memSize vs 64-bit pointer encoding inconsistency (filed task-0069, MEDIUM)

No aliasing-related unsoundness identified with current usage pattern (guards protect all accesses). The gaps become critical in Phase 3c (HeapLift) and Phase 3d (separation logic).

Differential testing confirms struct layouts match gcc for all 6 test structs.
<!-- SECTION:FINAL_SUMMARY:END -->
