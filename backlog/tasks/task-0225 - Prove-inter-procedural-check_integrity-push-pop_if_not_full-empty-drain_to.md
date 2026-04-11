---
id: TASK-0225
title: 'Prove inter-procedural: check_integrity, push/pop_if_not_full/empty, drain_to'
status: To Do
assignee: []
created_date: '2026-04-11 15:07'
updated_date: '2026-04-11 21:27'
labels:
  - sorry-elimination
  - inter-procedural
  - ring-buffer
dependencies:
  - TASK-0221
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
These functions call other ring buffer functions. Strategy: apply the callee's FuncSpec at the call site using L1_hoare_call_spec (from FuncSpec.lean). Prerequisites: the callee's validHoare must be proven first (rb_push for push_if_not_full, rb_pop for pop_if_not_empty, rb_count_nodes for check_integrity). drain_to calls both rb_pop and rb_push in a loop — the hardest inter-procedural proof.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 rb_check_integrity_validHoare proven (uses rb_count_nodes spec)
- [ ] #2 rb_push_if_not_full_validHoare proven (uses rb_push spec)
- [ ] #3 rb_pop_if_not_empty_validHoare proven (uses rb_pop spec)
- [ ] #4 rb_drain_to_validHoare proven (uses rb_pop + rb_push specs in loop)
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
AutoCorres2 insight: function calls become runs_to obligations. Callee spec is supplied as [runs_to_vcg] hint. Our equivalent: L1_hoare_call_spec from FuncSpec.lean. Need: callee validHoare proven first, then caller proof applies it via L1_hoare_call_spec.

Dependency: rb_check_integrity needs rb_count_nodes (proven). rb_push_if_not_full needs rb_push (not proven yet). rb_pop_if_not_empty needs rb_pop (not proven). rb_drain_to needs both rb_push + rb_pop in a loop.
<!-- SECTION:NOTES:END -->
