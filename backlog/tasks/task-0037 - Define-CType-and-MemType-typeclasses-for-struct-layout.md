---
id: TASK-0037
title: Define CType and MemType typeclasses for struct layout
status: To Do
assignee: []
created_date: '2026-04-08 21:38'
labels:
  - phase-3b
  - csemantics
dependencies:
  - TASK-0034
references:
  - ext/AutoCorres2/TypHeapSimple.thy
  - ext/AutoCorres2/c-parser/umm_heap/
  - Clift/CSemantics/TypeTag.lean
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Define typeclasses that encode C type layout: size, alignment, field offsets for structs, padding. These are generated per-struct by the CImporter. Study ext/AutoCorres2/c-parser for the original type representation. Must match the target platform ABI (start with x86-64 LP64).
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 CType typeclass with size, alignment methods defined
- [ ] #2 MemType typeclass with toBytes, fromBytes methods defined
- [ ] #3 CType instances for UInt8, UInt16, UInt32, UInt64
- [ ] #4 Struct layout calculation matches gcc sizeof/offsetof for test structs
- [ ] #5 Padding and alignment rules documented
<!-- AC:END -->
