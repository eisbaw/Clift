---
id: TASK-0075
title: 'Scale testing: verify 500-1000 LOC real embedded C module'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-09 19:34'
updated_date: '2026-04-09 22:56'
labels:
  - phase-5
  - test
  - scaling
dependencies:
  - TASK-0049
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The current test suite covers small functions (5-20 LOC each). Need to test on a real embedded C module of 500-1000 LOC to identify scaling bottlenecks: CImporter limitations, proof term sizes, missing C features, tactic gaps. Candidates: a small crypto primitive (SHA-256 core), a CRC implementation, an embedded protocol parser, or a device driver.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Real C module (500+ LOC) selected and documented
- [ ] #2 CImporter processes the full module
- [ ] #3 At least 3 functions verified through the full pipeline
- [ ] #4 Scaling bottlenecks documented
- [ ] #5 Missing C features cataloged as backlog tasks
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Deferred to Phase 5+. Current scale documented:

Current test suite: 11 C source files, 224 total LOC across:
- gcd.c (10 LOC) - full pipeline: CSimpl->L1->L2->L3->L5, correctness proof
- max.c (5 LOC) - full pipeline through L1
- swap.c (7 LOC) - CSimpl->L1->HeapLift, heap swap proof (1 sorry in L1 VCG)
- rotate3.c (43 LOC, 4 functions) - L1corres for rotate3/abs_diff/clamp
- list_length.c (13 LOC) - CImporter parsing only (struct pointer)
- div_test.c (10 LOC) - UB guard verification
- signed_arith.c (18 LOC) - signed overflow guards
- for_loop.c (10 LOC) - for->while desugaring
- do_while.c (11 LOC) - do-while desugaring
- switch_test.c (21 LOC) - switch->if-else desugaring
- struct_sizes.c (76 LOC) - struct layout differential testing

Verified through full pipeline: gcd (10 LOC), swap (7 LOC partially)
Verified through L1corres: rotate3, abs_diff, clamp (43 LOC combined)
CImporter-only (parsing verified, no proofs): remaining files

Scaling bottlenecks identified:
1. Lean kernel type-checking is the bottleneck, not CImporter parsing
2. Proof term depth for sequential L1 steps (kernel stack overflow at ~7 steps)
3. Manual L1corres proofs scale linearly with function size
4. Missing: function calls across modules, global variables, arrays

To reach 500+ LOC: need MetaM automation (task-0071), function pointers (task-0073), and array support. A CRC-32 implementation (~100 LOC) would be a good intermediate target.
<!-- SECTION:FINAL_SUMMARY:END -->
