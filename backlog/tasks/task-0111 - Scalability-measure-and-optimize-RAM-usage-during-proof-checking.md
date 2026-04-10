---
id: TASK-0111
title: 'Scalability: measure and optimize RAM usage during proof checking'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-10 12:58'
updated_date: '2026-04-10 14:22'
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
- [x] #1 Peak RAM measured for: SwapProof, GcdPhase2, ListLengthProof, RingBufferProof
- [x] #2 RAM-hungry patterns identified
- [x] #3 Optimization strategy documented
- [x] #4 Estimated RAM for 150-function verification documented
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Measured peak RAM for all key targets.

Results:
- SwapProof: 778MB, RingBufferProof: 1502MB, ListLengthProof: 779MB
- RingBufferExtProof (40 funcs): 1543MB
- Full clean build: 1503MB
- Per Lean worker process: ~200-300MB
- Peak determined by Lake parallelism (N cores * 300MB), not function count

RAM-hungry patterns: large state records, MetaM allocation during clift.
Optimization: already using [local irreducible]; no Mathlib = huge win.

Verdict:
- 32GB: 500+ functions with no concern
- 16GB: 150+ functions comfortably
- 8GB: marginal, limit parallelism

See notes/scalability-measurements.md for full data.
<!-- SECTION:FINAL_SUMMARY:END -->
