---
id: TASK-0067
title: Mechanize struct roundtrip proofs (eliminate sorry)
status: Done
assignee:
  - '@claude'
created_date: '2026-04-09 17:13'
updated_date: '2026-04-09 20:10'
labels:
  - phase-3c
  - proof
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Generated struct MemType instances (e.g. C_node) use sorry for the fromBytes/toBytes roundtrip proof. These need to be proven mechanically. The proof structure: show each field reads back correctly given the if-then-else dispatch in toBytes, using omega for the byte range conditions.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 C_node.fromBytes_toBytes proven (no sorry)
- [x] #2 Proof generator handles arbitrary struct shapes
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Eliminated the sorry in C_node.fromBytes_toBytes by mechanically generating the proof in the CImporter. The proof strategy: (1) for each field, prove a helper theorem showing toBytes at that field's byte range dispatches correctly via dif_pos/dif_neg, (2) the main theorem uses funext + the helpers to rewrite byte slices to field toBytes functions, then applies scalar roundtrip lemmas. The CImporter now generates these proofs for arbitrary struct shapes (not just C_node).
<!-- SECTION:FINAL_SUMMARY:END -->
