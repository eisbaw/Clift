---
id: TASK-0159
title: 'Example: verify a red-black tree (insert, delete, lookup, balance)'
status: To Do
assignee: []
created_date: '2026-04-10 18:47'
labels:
  - phase-n
  - examples
  - data-structures
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Red-black trees are the canonical complex data structure for verification. ~500 LOC with: insert, delete, lookup, min, max, in-order traversal. Prove: BST property, color invariant (no two consecutive reds), black-height balance, lookup correctness. This exercises: pointer-heavy code, recursive data structures, complex invariants, multiple interacting properties.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Red-black tree C source (500+ LOC)
- [ ] #2 BST property proven for insert/delete
- [ ] #3 Color invariant proven
- [ ] #4 Black-height balance proven
- [ ] #5 Lookup correctness: find(insert(t, k, v), k) = Some v
- [ ] #6 No sorry
<!-- AC:END -->
