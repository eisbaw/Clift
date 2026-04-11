---
id: TASK-0230
title: Document the sorry elimination playbook
status: To Do
assignee: []
created_date: '2026-04-11 15:07'
labels:
  - documentation
  - sorry-elimination
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Capture everything we learned about eliminating sorry into a single reference document. For each sorry category (pure, heap accessor, multi-step heap, loop, conditional, inter-procedural): the exact tactic sequence, which L1HoareRules lemmas to use, when to use [local irreducible], how to write projection lemmas, common pitfalls (kernel depth, subst expansion, 40-field Locals). Include the rb_count_nodes proof as the loop template and the SwapProof as the heap template. This is the document that future sessions (or the Claude proof engine) need to efficiently eliminate sorry.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Playbook in docs/sorry-elimination-playbook.md
- [ ] #2 One section per sorry category with exact tactic sequence
- [ ] #3 Worked example for each category
- [ ] #4 Common pitfalls and workarounds documented
- [ ] #5 Which L1HoareRules lemmas to use for each pattern
<!-- AC:END -->
