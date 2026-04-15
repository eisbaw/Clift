---
id: TASK-0277
title: 'Paper: fix consistency issues (terminology, formatting, cross-refs)'
status: Done
assignee: []
created_date: '2026-04-15 07:29'
updated_date: '2026-04-15 07:43'
labels:
  - paper
  - consistency
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Consistency reviewer found: (1) sorry sometimes plain, sometimes texttt. (2) Lean 4 missing tilde in 4 places. (3) AutoCorres vs AutoCorres2 inconsistent. (4) CImporter formatting inconsistent. (5) Hard-coded Section 3.5 needs label/ref. (6) MetaM, SpecM, mvcgen, Std.Do.Triple missing texttt.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 All sorry in texttt format
- [x] #2 All Lean~4 with tilde
- [x] #3 Hard-coded section refs replaced with label/ref
- [x] #4 All code identifiers in texttt
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
All bare sorry now in texttt. Fixed 2 Lean~4 missing tildes. Replaced hard-coded Section~3.5 with label/ref. Added texttt to MetaM, SpecM, mvcgen.
<!-- SECTION:FINAL_SUMMARY:END -->
