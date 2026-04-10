---
id: TASK-0100
title: AI data structure invariant generation
status: To Do
assignee: []
created_date: '2026-04-10 05:19'
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
- [ ] #1 ai_struct_invariant tactic: given struct + operations, propose invariant
- [ ] #2 Tested on linked list (next pointers form acyclic chain)
- [ ] #3 Tested on array-backed queue (head/tail wrap correctly)
- [ ] #4 Measured: success rate (target >50%)
- [ ] #5 All invariants kernel-checked
<!-- AC:END -->
