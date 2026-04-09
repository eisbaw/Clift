---
id: TASK-0051
title: 'Document ADR: Inductive WhileResult/WhileFail vs Fin-indexed chains'
status: To Do
assignee: []
created_date: '2026-04-08 22:36'
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
- [ ] #1 ADR file created under backlog/docs/
<!-- AC:END -->
