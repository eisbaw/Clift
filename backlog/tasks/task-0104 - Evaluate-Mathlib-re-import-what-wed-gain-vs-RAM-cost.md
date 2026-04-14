---
id: TASK-0104
title: 'Evaluate Mathlib re-import: what we''d gain vs RAM cost'
status: To Do
assignee: []
created_date: '2026-04-10 12:58'
updated_date: '2026-04-14 22:12'
labels:
  - infrastructure
  - scalability
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
We dropped Mathlib (ADR-002) to reduce RAM from 9GB to <500MB per Lean process. But Mathlib has: (1) BitVec/UInt extensive lemma library — would eliminate our manual UInt8/16/32/64 ext theorems and byte encoding proofs, (2) Finset/Finmap — cleaner modifies-set representation, (3) by_contra/push_neg/not_not — tactics we had to work around, (4) Data.List — extensive list lemmas for linked list proofs, (5) Algebra — CommRing etc for grind integration, (6) Order — lattice/complete lattice for separation logic. Cost: 9GB+ RAM per process, Mathlib version churn. Mitigation for RAM: use lake exe cache get (prebuilt oleans, no recompilation). Evaluate whether the proof simplification justifies the RAM cost. Key question: does Mathlib prebuilt cache reduce RAM to acceptable levels?
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Measured: RAM usage with Mathlib prebuilt cache (lake exe cache get) vs without
- [ ] #2 Listed: which Mathlib lemmas would replace our manual proofs
- [ ] #3 Listed: which proofs become shorter with Mathlib
- [ ] #4 Decision documented as ADR update or new ADR
- [ ] #5 If re-importing: all existing proofs still compile
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Decision: keep Mathlib out. Re-evaluate after tasks 0105 (MetaM VCG) and 0112 (Claude benchmark).

Rationale:
- Current build: 0.4s, ~500MB RAM. With Mathlib: ~60s, 2-4GB (cached) or 9GB (from source).
- Mathlib helps with ~20 manual lemmas (UInt ext, Set basics) — already solved in 200 LOC.
- Mathlib does NOT help with the bottleneck (mechanical L1 stepping — 80% of proof effort).
- Version churn risk is real for a 40+ week project.

When to re-import:
- If MetaM VCG (0105) eliminates L1 stepping, remaining effort shifts to arithmetic/data structures where Mathlib helps.
- If Claude benchmark (0112) shows Claude needs Mathlib lemmas for proof generation.
- If grind + Mathlib @[grind] lemmas would close goals our custom tactics can't.
<!-- SECTION:FINAL_SUMMARY:END -->
