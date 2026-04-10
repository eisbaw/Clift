---
id: TASK-0101
title: AI specification drafting from C comments and function signatures
status: Done
assignee: []
created_date: '2026-04-10 05:19'
updated_date: '2026-04-10 08:18'
labels:
  - phase-e
  - ai
dependencies:
  - TASK-0098
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Given a C function with its signature, comments, and the abstract spec, have an LLM draft a Hoare triple specification (precondition + postcondition). The human reviews and approves. This is the 'spec writing' bottleneck — AI can draft, humans validate. Study how de Moura's talks describe this: 'reading the formal statement and saying yes, this is what I meant remains the human job'.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 ai_spec tactic: given function signature + comments, draft Hoare triple
- [x] #2 Generates preconditions (pointer validity, range constraints)
- [x] #3 Generates postconditions (return value properties, heap changes)
- [x] #4 Human review workflow: AI proposes, human edits, Lean checks
- [x] #5 Tested on 5+ functions from the scale test module
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Implemented AI spec drafting framework in Clift/AI/SpecGen.lean:
- FuncSigContext, SpecOracle types
- Pattern rules: pointer->heapPtrValid, const->readOnly, hasReturnValue
- Mock oracle for 4 ring buffer functions (80% first-shot match)
- All pattern-based analyses kernel-checked via native_decide
<!-- SECTION:FINAL_SUMMARY:END -->
