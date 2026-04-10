---
id: TASK-0111
title: 'Scalability: measure and optimize RAM usage during proof checking'
status: To Do
assignee: []
created_date: '2026-04-10 12:58'
labels:
  - scalability
  - performance
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Lean 4 processes used 9GB+ with Mathlib and 21GB during deep kernel reduction. At seL4 scale, multiple files will be checked. Need: (1) measure peak RAM per file as function complexity grows, (2) identify which proofs are RAM-hungry (heapPtrValid unfolding? large proof terms?), (3) optimize: can we use opaque/irreducible more aggressively? split large proofs into separate modules? (4) determine: can we verify seL4-scale C on a 32GB machine?
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Peak RAM measured for: SwapProof, GcdPhase2, ListLengthProof, RingBufferProof
- [ ] #2 RAM-hungry patterns identified
- [ ] #3 Optimization strategy documented
- [ ] #4 Estimated RAM for 150-function verification documented
<!-- AC:END -->
