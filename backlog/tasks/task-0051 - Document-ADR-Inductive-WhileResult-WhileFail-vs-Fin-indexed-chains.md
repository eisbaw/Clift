---
id: TASK-0051
title: 'Document ADR: Inductive WhileResult/WhileFail vs Fin-indexed chains'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-08 22:36'
updated_date: '2026-04-09 19:45'
labels:
  - adr
  - phase-0
dependencies: []
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Record the architectural decision to use inductive predicates (WhileResult/WhileFail) for encoding while loop semantics in NondetM, instead of Fin-indexed state chains. The inductive approach made proofs dramatically simpler (particularly hoare_while_total) and is more natural for induction.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 ADR file created under backlog/docs/
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Created backlog/docs/adr-003-while-semantics.md documenting the decision to use inductive WhileResult/WhileFail predicates instead of Fin-indexed state chains. Documents the rationale (structural induction, clean base cases, mirrors Exec pattern) and the limitations (least fixed point gives partial correctness only).
<!-- SECTION:FINAL_SUMMARY:END -->
