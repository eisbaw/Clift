---
id: TASK-0096
title: Global invariant framework
status: To Do
assignee: []
created_date: '2026-04-10 05:19'
labels:
  - phase-d
  - verification-infrastructure
dependencies:
  - TASK-0095
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
seL4's biggest proof effort (~80%) was invariant proofs: showing that global invariants hold across ALL functions. Define a framework for global invariants: (1) state the invariant (a predicate on CState), (2) prove each function preserves it, (3) compose into a system-wide invariant theorem. The VCG should generate invariant-preservation obligations automatically. Without this, each function proof is isolated and doesn't contribute to system-level assurance.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 GlobalInvariant type: CState -> Prop
- [ ] #2 invariant_preserved theorem shape: {inv /\ P} f {inv /\ Q}
- [ ] #3 VCG generates invariant obligations automatically
- [ ] #4 Invariant composition: if all functions preserve inv, system preserves inv
- [ ] #5 Example: memory allocator invariant (free list well-formed)
<!-- AC:END -->
