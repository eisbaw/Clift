---
id: TASK-0219
title: 'Formal TCB minimality argument: prove our TCB is no larger than seL4''s'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-11 06:29'
updated_date: '2026-04-11 07:26'
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
- [x] #1 TCB comparison document: Clift vs seL4 component by component
- [x] #2 Size comparison: lines of trusted code
- [x] #3 Argument for each TCB component: why it's trustworthy
- [x] #4 Mitigation for each trust gap
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Wrote TCB minimality argument in docs/tcb-minimality.md. Line-by-line comparison with seL4, size estimates, trust arguments for each component, mitigation for each gap.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Wrote docs/tcb-minimality.md: formal TCB minimality argument.

Covers:
- Component-by-component comparison: Clift vs seL4
- 5 components: proof kernel, C parser, compiler, hardware, ASM/platform
- Size comparison: ~12K unique LOC (Clift) vs ~17K (seL4)
- Trust argument for each component
- 4 trust gaps with mitigations
- Conclusion: Clift TCB comparable, potentially smaller due to clang outsourcing
<!-- SECTION:FINAL_SUMMARY:END -->
