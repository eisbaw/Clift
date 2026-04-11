---
id: TASK-0219
title: 'Formal TCB minimality argument: prove our TCB is no larger than seL4''s'
status: To Do
assignee: []
created_date: '2026-04-11 06:29'
labels:
  - maturity
  - documentation
  - tcb
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
seL4's TCB is: Isabelle kernel + C parser + ~340 lines ASM + hardware assumptions. Our TCB is: Lean 4 kernel + CImporter + clang + hardware assumptions. Formally argue (in a document, not a proof) that our TCB is comparable in size and trust: (1) Lean kernel vs Isabelle kernel, (2) CImporter vs StrictC parser, (3) clang AST vs direct C parsing. A reviewer will ask: why should I trust Clift's TCB?
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 TCB comparison document: Clift vs seL4 component by component
- [ ] #2 Size comparison: lines of trusted code
- [ ] #3 Argument for each TCB component: why it's trustworthy
- [ ] #4 Mitigation for each trust gap
<!-- AC:END -->
