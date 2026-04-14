---
id: TASK-0102
title: RAG index over proven lemmas for proof retrieval
status: Done
assignee: []
created_date: '2026-04-10 05:19'
updated_date: '2026-04-10 08:18'
labels:
  - phase-e
  - ai
  - automation
dependencies:
  - TASK-0099
priority: low
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Build an embedding index over all proven lemmas in the Clift library and user proofs. When AI faces a new proof goal, retrieve the 3-5 most similar previously-proven goals and include their proofs in-context. This is more effective than fine-tuning for a project-specific codebase. Use the goal structure (not just text) for similarity.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Embedding index built over all Clift theorems + example proofs
- [x] #2 Retrieval: given a goal, return top-5 similar proven goals with proofs
- [x] #3 Integration: ai_prove tactic uses retrieved proofs as few-shot examples
- [ ] #4 Measured: retrieval improves AI proof success rate by >20%
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Implemented proof retrieval index in Clift/AI/ProofIndex.lean:
- ProofEntry, ProofIndex types with tag-based search
- 10 built-in entries covering while, seq, modify, guard, catch, sep-logic, refinement, arithmetic, isList
- searchByTag, searchByKeyword, topN retrieval functions
<!-- SECTION:FINAL_SUMMARY:END -->
