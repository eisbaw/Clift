---
id: TASK-0037
title: Define CType and MemType typeclasses for struct layout
status: Done
assignee:
  - '@mped'
created_date: '2026-04-08 21:38'
updated_date: '2026-04-09 17:00'
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
- [x] #1 CType typeclass with size, alignment methods defined
- [x] #2 MemType typeclass with toBytes, fromBytes methods defined
- [x] #3 CType instances for UInt8, UInt16, UInt32, UInt64
- [x] #4 Struct layout calculation matches gcc sizeof/offsetof for test structs
- [x] #5 Padding and alignment rules documented
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
1. Add UInt8/UInt16/UInt64 extensionality theorems in Util/
2. Add MemType instances for UInt8, UInt16, UInt64 in State.lean
3. Add Ptr MemType instance (8 bytes, x86-64 LP64)
4. Add StructField descriptor and layout computation (size, alignment, padding)
5. Document alignment rules
6. Build and verify all proofs
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
UInt8/16/64 extensionality theorems added in Util/.
MemType instances for UInt8, UInt16, UInt64, Ptr added.
StructField descriptor and computeStructLayout added.
Ptr roundtrip proof required careful handling of dependent Fin types.
alignUp_ge proof needed explicit Nat.mul_comm to help omega.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Added CType/MemType infrastructure for struct layout:
- UInt8Ext, UInt16Ext, UInt64Ext extensionality theorems in Util/
- MemType instances for UInt8 (1B), UInt16 (2B LE), UInt32 (4B LE), UInt64 (8B LE)
- Ptr MemType instance (8 bytes, x86-64 LP64)
- StructField descriptor and computeStructLayout with gcc x86-64 ABI alignment rules
- alignUp utility with proof of monotonicity
- All proofs verified (no sorry, no axiom beyond propext/Quot.sound)
<!-- SECTION:FINAL_SUMMARY:END -->
