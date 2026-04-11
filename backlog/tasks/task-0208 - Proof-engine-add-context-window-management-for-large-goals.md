---
id: TASK-0208
title: 'Proof engine: add context window management for large goals'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-11 06:28'
updated_date: '2026-04-11 08:45'
labels:
  - proof-engine
  - ai
dependencies:
  - TASK-0204
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Some validHoare goals have large contexts (20+ hypotheses, complex types). The prompt must fit in Claude's context window while including: goal state, relevant definitions, [local irreducible] hint, similar proofs, function body. Build intelligent context selection: rank hypotheses by relevance, truncate large types, include only referenced definitions.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Context window budget tracked (target: <8K tokens per prompt)
- [ ] #2 Hypothesis ranking by relevance to goal
- [ ] #3 Type truncation for display
- [ ] #4 Tested on goals with 20+ hypotheses
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Design spec written: docs/proof-engine-context-management.md. Covers hypothesis ranking by relevance (direct/type/transitive scoring), type truncation for large structs, definition selection strategy, similar proof selection from ProofIndex, and budget management (<8K tokens per prompt). Implementation plan with 6 steps. No code implementation -- this is a design task.
<!-- SECTION:FINAL_SUMMARY:END -->
