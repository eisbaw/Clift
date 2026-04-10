---
id: TASK-0112
title: 'Claude-as-proof-engine: benchmark Claude on Clift proof obligations'
status: To Do
assignee: []
created_date: '2026-04-10 12:58'
labels:
  - ai
  - scalability
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Claude is good at writing Lean proofs. Our proof-to-code ratio (8-16:1) means lots of proof code — but if Claude writes it, the ratio matters less than whether Claude can CORRECTLY write it. Benchmark: take 20 proof obligations from our test suite, prompt Claude with the goal state + context, measure: (1) first-attempt success rate, (2) success rate with 3 retries + error feedback, (3) types of errors (syntax? wrong lemma? timeout?). This determines whether Claude can be the proof engine at seL4 scale.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 20 proof obligations selected (mix of easy/medium/hard)
- [ ] #2 First-attempt success rate measured
- [ ] #3 3-retry success rate measured (with error feedback)
- [ ] #4 Error categorization: syntax, wrong lemma, timeout, deep recursion
- [ ] #5 Estimated: what % of seL4-scale proof could Claude write?
- [ ] #6 Bottleneck identified: what proof patterns does Claude fail on?
<!-- AC:END -->
