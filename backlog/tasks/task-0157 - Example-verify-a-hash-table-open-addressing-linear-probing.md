---
id: TASK-0157
title: 'Example: verify a hash table (open addressing, linear probing)'
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
Hash tables are ubiquitous in systems code. Write a ~300 LOC hash table with: init, insert, lookup, delete, resize. Uses array subscript, modular arithmetic, pointer manipulation. Prove: lookup after insert returns the inserted value, delete removes the entry, no false positives, invariant (no duplicate keys, load factor bounded). Exercises array support + modular arithmetic.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Hash table C source (300+ LOC) with 5+ functions
- [ ] #2 CImporter processes successfully
- [ ] #3 Abstract spec: partial function (Key -> Option Value)
- [ ] #4 insert/lookup correctness proven
- [ ] #5 Invariant: no duplicate keys
- [ ] #6 No sorry
<!-- AC:END -->
