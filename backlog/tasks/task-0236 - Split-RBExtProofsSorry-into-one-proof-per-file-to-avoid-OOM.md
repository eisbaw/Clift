---
id: TASK-0236
title: Split RBExtProofsSorry into one-proof-per-file to avoid OOM
status: Done
assignee: []
created_date: '2026-04-12 18:58'
updated_date: '2026-04-12 22:40'
labels:
  - infrastructure
  - scaling
  - sorry-elimination
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
RBExtProofsSorry.lean has 14 sorry. When agents replace sorry with actual proofs, the file OOMs (>30GB) because each loop proof with 40-field Locals step functions costs ~3-5GB elaboration. With 5+ proofs in one file, total exceeds 30GB.

THE FILE WITH SORRY BUILDS FINE (~2GB). The OOM is from accumulated proof terms, not the sorry.

EVIDENCE:
- RBExtProofsSimple.lean: 7 simple proofs, builds ~3GB — OK
- RBExtProofsLoops.lean: 8 loop proofs, builds ~12GB — OK (close to limit)
- RBExtProofsLoops2.lean: 2 loop proofs, builds ~8GB — OK
- RBExtProofsSorry.lean with 3+ proofs replaced: >30GB — OOM

AGENTS WROTE CORRECT PROOFS THAT OOM:
- rb_swap_front_back: aef12e4 agent proved it (0 sorry), build OOM'd
- rb_pop: a3e6e62 agent proved parts 1+2, only 1 sorry remains (typeclass issue)
- rb_increment_all..rb_clear: abbade2 agent eliminated ALL 13 sorry in one run, build OOM'd
- rb_check_integrity, rb_push_if_not_full, rb_pop_if_not_empty: blocked by dynCom (TASK-0235), not OOM

FIX: Split each provable sorry into its own file:

1. RBExtProofPop.lean — rb_pop (parts 1+2 proven, 1 sorry in guard+modify decomposition)
2. RBExtProofSwapFrontBack.lean — rb_swap_front_back (fully proven by aef12e4 agent)
3. RBExtProofIncrementAll.lean — rb_increment_all (proven by abbade2 agent)
4. RBExtProofReplaceAll.lean — rb_replace_all (proven by abbade2 agent)
5. RBExtProofFill.lean — rb_fill (proven by abbade2 agent)
6. RBExtProofReverse.lean — rb_reverse (proven by abbade2 agent)
7. RBExtProofRemoveFirstMatch.lean — rb_remove_first_match (proven by abbade2 agent)
8. RBExtProofEqual.lean — rb_equal (proven by abbade2 agent)
9. RBExtProofClear.lean — rb_clear (proven by abbade2 agent)
10. RBExtProofIterSkip.lean — rb_iter_skip (proven by abbade2 agent)
11. RBExtProofCheckIntegrity.lean — rb_check_integrity (blocked on TASK-0235 dynCom)
12. RBExtProofPushIfNotFull.lean — rb_push_if_not_full (blocked on TASK-0235 dynCom)
13. RBExtProofPopIfNotEmpty.lean — rb_pop_if_not_empty (blocked on TASK-0235 dynCom)
14. RBExtProofDrainTo.lean — rb_drain_to (blocked on TASK-0235 dynCom)

Each file:
- imports Examples.RBExtSpecs
- proves exactly 1 theorem
- builds in ~5GB (well within 30GB limit)
- can be built independently: lake build Examples.RBExtProofSwapFrontBack

IMPLEMENTATION APPROACH:
1. Create each file with the theorem statement + sorry
2. Re-apply the agent's proven proofs from the transcript logs:
   - abbade2 agent transcript: /tmp/claude-1000/.../tasks/abbade2ee4a048551.output
   - aef12e4 agent transcript: /tmp/claude-1000/.../tasks/aef12e413174fc0e1.output
   - a3e6e62 agent transcript: /tmp/claude-1000/.../tasks/a3e6e62296ab0f306.output
3. Build each file individually to verify
4. Update lakefile.lean with new modules
5. Update CI pipeline with per-proof build jobs
6. Keep RBExtProofsSorry.lean for dynCom-blocked sorry (or delete and put those in individual files too)

MEMORY BUDGET: Each file must build in <10GB. If a single proof exceeds 10GB, it needs further decomposition (extract step functions into a shared helper file).
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Each of the 14 sorry in its own .lean file
- [ ] #2 All previously-proven sorry (swap_front_back, increment_all, etc.) re-applied from agent transcripts
- [ ] #3 Each file builds independently in <10GB RAM
- [ ] #4 lakefile.lean updated with all new modules
- [ ] #5 Sorry count unchanged (proofs moved, not lost)
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
14 sorry split into one-proof-per-file. 10 of 14 subsequently proven (swap_front_back, increment_all, replace_all, fill, reverse, remove_first_match, equal, iter_skip, iter_next, clear). 4 remain blocked on dynCom (TASK-0235).
<!-- SECTION:FINAL_SUMMARY:END -->
