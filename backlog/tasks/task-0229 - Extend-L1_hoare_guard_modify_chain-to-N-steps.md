---
id: TASK-0229
title: Extend L1_hoare_guard_modify_chain to N steps
status: To Do
assignee: []
created_date: '2026-04-11 15:07'
labels:
  - automation
  - infrastructure
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
We have chain2 (2 guard+modify pairs) and chain3 (3 pairs). rb_push needs 8+ pairs. Instead of writing chain4, chain5, ..., chain8, write a general N-step chain using a list of guard/modify pairs and recursion. Or: write chain4 and chain5 (the max practical nesting before kernel depth), then compose chain5 with chain3 for 8-step. The L1_seq_modify_modify approach (fusing into one modify) is the alternative — define the composed function f = fN ∘ ... ∘ f1 explicitly and prove one guard_modify_fused for the whole chain.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Either: chainN for arbitrary N, or chain4+chain5 for practical coverage
- [ ] #2 rb_push's 8-step chain expressible using these lemmas
- [ ] #3 All chain lemmas proven with zero sorry
<!-- AC:END -->
