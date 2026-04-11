---
id: TASK-0226
title: Prove remaining totalHoare from proven validHoare + Terminates
status: To Do
assignee: []
created_date: '2026-04-11 15:07'
labels:
  - sorry-elimination
  - total-correctness
dependencies:
  - TASK-0221
  - TASK-0222
priority: low
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
For each function where validHoare is proven and Terminates is proven, totalHoare follows by definition (totalHoare = validHoare ∧ terminates). Pattern: unfold totalHoare, exact ⟨validHoare_proof, terminates_proof⟩. Some functions need new Terminates proofs. Use the Terminates rules from TerminatesProps.lean.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 All totalHoare theorems for functions with proven validHoare + Terminates are closed
- [ ] #2 New Terminates proofs added where needed
<!-- AC:END -->
