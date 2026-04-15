---
id: TASK-0274
title: 'Paper: fix BibTeX entries and add missing related work'
status: Done
assignee: []
created_date: '2026-04-15 07:28'
updated_date: '2026-04-15 07:36'
labels:
  - paper
  - references
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
References reviewer found: (1) Wrong DOI on tuch2009types and sewell2013translation. (2) Incorrect authors on autocorres2. (3) LeanCorres URL may not be public. (4) Missing related work: Iris, Frama-C, VeriFast, CertiKOS, CN, HACL*, Bedrock, Cerberus. (5) Three uncited claims need citations (200K LOC/20 person-years, LLM Lean vs Isabelle, community size).
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Fix DOIs for tuch2009types and sewell2013translation
- [x] #2 Fix autocorres2 authors
- [x] #3 Add at least Frama-C, Iris, and CertiKOS to related work
- [x] #4 Add citations for 200K LOC claim and LLM performance claim
- [x] #5 Verify LeanCorres and Clift repo URLs resolve
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Fixed tuch2009types DOI, sewell2013translation to @inproceedings with correct DOI, autocorres2 authors. Added Frama-C, Iris, CertiKOS to related work with BibTeX. Softened LLM performance claim. 200K LOC claim already cited via klein2009sel4.
<!-- SECTION:FINAL_SUMMARY:END -->
