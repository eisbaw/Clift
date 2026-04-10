---
id: TASK-0132
title: 'Specification library: reusable specs for common patterns'
status: To Do
assignee: []
created_date: '2026-04-10 15:30'
labels:
  - phase-j
  - library
  - industrial
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Industrial users shouldn't write specs from scratch. Build a library of reusable specs: (1) FIFO queue, (2) LIFO stack, (3) hash map, (4) ring buffer, (5) state machine, (6) memory allocator, (7) sorted container. Each spec: abstract type + operations + properties + invariant template. Users instantiate for their concrete C data structure.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 At least 5 reusable abstract specs in Clift/Specs/
- [ ] #2 Each spec: state type, operations, properties, invariant
- [ ] #3 Instantiation example for each spec
- [ ] #4 Documented: how to adapt a spec to your data structure
<!-- AC:END -->
