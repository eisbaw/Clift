---
id: TASK-0034
title: Extend HeapRawState with heap type descriptor (htd)
status: Done
assignee:
  - '@mped'
created_date: '2026-04-08 21:37'
updated_date: '2026-04-09 05:47'
labels:
  - phase-3a
  - csemantics
dependencies:
  - TASK-0032
references:
  - ext/AutoCorres2/TypHeapSimple.thy
  - Clift/CSemantics/State.lean
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Extend HeapRawState with a proper heap type descriptor that tracks what type is stored at each address. Define heapPtrValid predicate. Define hVal (read typed value from raw bytes). Study ext/AutoCorres2/TypHeapSimple.thy for the simplified model.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 HeapRawState.htd field tracks type at each address
- [x] #2 heapPtrValid p s defined: pointer p is valid in state s
- [x] #3 hVal s p : read typed value from raw bytes at pointer address
- [x] #4 heapUpdate s p v : write typed value to raw bytes
- [x] #5 Basic lemma: hVal (heapUpdate s p v) p = v proven
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
1. Add MemType instance for UInt32 with encode/decode
2. Define heapPtrValid: pointer p is valid when htd matches and alignment ok
3. Define hVal: read CType.size bytes from mem, decode
4. Define heapUpdate: encode value, write bytes to mem
5. Prove hVal_heapUpdate: hVal (heapUpdate s p v) p = v
6. Prove heapUpdate_other: disjoint pointers => hVal (heapUpdate s p v) q = hVal s q
7. lake build
<!-- SECTION:PLAN:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Extended HeapRawState with typed heap operations for Phase 3a.

Changes in Clift/CSemantics/State.lean:
- Added MemType typeclass with fromMem/toMem + roundtrip law (replaces skeleton)
- Added CType.size_pos proof obligation
- Implemented UInt32 MemType instance with little-endian byte encoding
- Added Ptr.null, Ptr DecidableEq, ptrDisjoint
- Defined heapPtrValid predicate (htd match + non-null + bounds)
- Defined readMemSlice/writeMemSlice for byte-level memory access
- Defined hVal (typed read) and heapUpdate (typed write)
- Proved hVal_heapUpdate_same: read-after-write returns written value
- Proved hVal_heapUpdate_disjoint: disjoint writes dont affect reads

Key design decision: MemType uses Fin-indexed functions (fromMem : Fin size -> UInt8 -> a) rather than List-based encode/decode. This keeps everything computable and avoids List length proof obligations.

All proofs axiom-free (only propext, Quot.sound from Lean core).
<!-- SECTION:FINAL_SUMMARY:END -->
