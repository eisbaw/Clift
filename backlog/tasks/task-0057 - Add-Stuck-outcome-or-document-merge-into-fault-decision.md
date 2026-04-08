---
id: TASK-0057
title: Add Stuck outcome or document merge-into-fault decision
status: To Do
assignee: []
created_date: '2026-04-08 22:55'
labels:
  - design
  - csemantics
dependencies: []
priority: low
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Simpl has 4 outcomes: Normal, Abrupt, Fault, Stuck. Our Outcome has 3, merging Stuck into fault. This is a deliberate simplification. Either add Stuck as a separate outcome (cleaner separation of UB vs stuck) or document the merge as an ADR.
<!-- SECTION:DESCRIPTION:END -->
