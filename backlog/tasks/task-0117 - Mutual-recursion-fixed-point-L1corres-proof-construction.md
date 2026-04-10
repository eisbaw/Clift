---
id: TASK-0117
title: 'Mutual recursion: fixed-point L1corres proof construction'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-10 15:29'
updated_date: '2026-04-10 17:21'
labels:
  - phase-f
  - lifting
  - critical-path
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Complete the mutual recursion gap. Currently 4/40 functions lack L1corres because they call other functions. Need: well-founded induction on call depth (or fuel-based with termination proof). The call graph is acyclic for ring_buffer_ext — this should be solvable with the existing topological sort by proving that all callees' L1corres are available before the caller's proof. If genuinely cyclic: use Lean 4's mutual/partial def + termination_by.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 All 40 ring_buffer_ext functions have L1corres proofs
- [x] #2 Topological order ensures callee corres available before caller
- [x] #3 Cyclic call graphs handled (at least: detected and reported)
- [x] #4 No sorry
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
All 40 RingBufferExt functions now have L1corres proofs (was 36/40).
Key changes:
- Added L1corres_call_single theorem (targeted, per-callee)
- Rewrote corres_auto as MetaM tactic (not macro) for goal inspection
- corres_auto now looks up callee corres proofs by name convention in env
- ProcEnv/L1ProcEnv lookups discharged via simp with decide:=true
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
L1corres proofs now generated for ALL functions including call-containing ones.

Changes:
- Clift/Lifting/SimplConv.lean: Added L1corres_call_single theorem that only requires the specific callee to be in the L1ProcEnv (vs L1corres_call which requires ALL procedures)
- Clift/Tactics/CorresAuto.lean: Rewrote corres_auto from a macro to a proper MetaM tactic that inspects goals, looks up callee corres proofs by name convention in the environment, and applies L1corres_call_single
- Clift/Lifting/L1Auto.lean: Passes callee corres names to proveOneFunctionCorres

Results:
- RingBufferExt: 40/40 L1corres proofs (was 36/40)
- RingBuffer: 16/16 (was 15/16)
- MultiCall: 5/5 (was 2/5)
- No sorry in any corres proof
- Build time unchanged (~10s for full pipeline)
<!-- SECTION:FINAL_SUMMARY:END -->
