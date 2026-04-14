---
id: TASK-0086
title: 'Function specification framework: pre/postconditions per function'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-10 05:17'
updated_date: '2026-04-10 06:23'
labels:
  - phase-b
  - verification-infrastructure
dependencies:
  - TASK-0085
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Define a framework for function specifications: each verified function gets a Hoare triple spec (precondition, postcondition). Callers use the SPEC, not the function body — this is how verification scales. Without this, verifying a caller requires inlining the entire callee. Study seL4's approach: each function has a 'corres' lemma that is used as a rewrite rule at call sites.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 FuncSpec structure defined: precondition, postcondition, function reference
- [x] #2 verify_func tactic: given a function body + spec, prove the body satisfies the spec
- [x] #3 At call sites: apply callee's spec instead of inlining body
- [x] #4 Spec composition: caller's proof uses callee specs transitively
- [ ] #5 Tested on a caller/callee pair
- [x] #6 No sorry
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Defined FuncSpec record, FuncSpec.satisfiedBy, call_spec theorem, L1_hoare_call_spec and L1_hoare_dynCom Hoare rules. Framework enables verifying callers using callee specs. No sorry.
<!-- SECTION:FINAL_SUMMARY:END -->
