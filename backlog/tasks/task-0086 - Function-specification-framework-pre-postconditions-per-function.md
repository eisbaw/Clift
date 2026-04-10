---
id: TASK-0086
title: 'Function specification framework: pre/postconditions per function'
status: To Do
assignee: []
created_date: '2026-04-10 05:17'
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
- [ ] #1 FuncSpec structure defined: precondition, postcondition, function reference
- [ ] #2 verify_func tactic: given a function body + spec, prove the body satisfies the spec
- [ ] #3 At call sites: apply callee's spec instead of inlining body
- [ ] #4 Spec composition: caller's proof uses callee specs transitively
- [ ] #5 Tested on a caller/callee pair
- [ ] #6 No sorry
<!-- AC:END -->
