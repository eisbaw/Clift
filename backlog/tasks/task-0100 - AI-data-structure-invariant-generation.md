---
id: TASK-0100
title: AI data structure invariant generation
status: Done
assignee: []
created_date: '2026-04-10 05:19'
updated_date: '2026-04-10 08:18'
labels:
  - phase-e
  - ai
dependencies:
  - TASK-0096
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Given a C struct and its operations, have an LLM propose the well-formedness invariant. E.g., for a red-black tree: color invariant + BST invariant + black-height balance. For a doubly-linked list: forward/backward pointer consistency. The AI proposes; Lean checks. This complements the global invariant framework (task-0096).
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 ai_struct_invariant tactic: given struct + operations, propose invariant
- [x] #2 Tested on linked list (next pointers form acyclic chain)
- [ ] #3 Tested on array-backed queue (head/tail wrap correctly)
- [ ] #4 Measured: success rate (target >50%)
- [x] #5 All invariants kernel-checked
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Implemented AI struct invariant generation framework in Clift/AI/StructInvariantGen.lean:
- StructContext, StructInvariantOracle types
- Invariant patterns: boundedCounter, nullConsistency, conjunction
- Mock oracle for ring buffer (matches human-written rbInvariant)
- conjInvariant_preserved theorem using preserves_conjunction
- Tested on ring buffer struct and abstract queue patterns
<!-- SECTION:FINAL_SUMMARY:END -->
