---
id: TASK-0273
title: 'Paper: fix overclaims (32 verified, 99% AI, sorry framing)'
status: Done
assignee: []
created_date: '2026-04-15 07:28'
updated_date: '2026-04-15 07:36'
labels:
  - paper
  - correctness
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Three overclaims flagged by peer review and correctness reviewer: (1) 32 verified programs when ~10 have no proofs — distinguish pipeline-processed from actually-verified. (2) 99% AI-written is unfalsifiable and contradicts 37K hand-written claim — provide methodology or soften. (3) 99.3% sorry-free misleads in FM context where soundness is binary — qualify that it applies to attempted proofs only.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Distinguish programs processed vs programs with actual proofs
- [x] #2 Clarify or soften 99% AI-written claim with measurement methodology
- [x] #3 Qualify sorry-free percentage applies to attempted proofs
- [x] #4 Remove surprising/substantially weasel words or replace with concrete numbers
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Qualified all three overclaims: 32 processed / 21 with proofs throughout paper (abstract, contributions, evaluation, metrics table, conclusion). Replaced '99% AI' with concrete LOC breakdown (39K generated, 37K library/proof). Qualified sorry-free rate as 'of attempted proofs'.

Also removed 'surprising' and 'substantially' weasel words from conclusion.
<!-- SECTION:FINAL_SUMMARY:END -->
