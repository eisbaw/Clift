---
id: TASK-0101
title: AI specification drafting from C comments and function signatures
status: To Do
assignee: []
created_date: '2026-04-10 05:19'
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
- [ ] #1 ai_spec tactic: given function signature + comments, draft Hoare triple
- [ ] #2 Generates preconditions (pointer validity, range constraints)
- [ ] #3 Generates postconditions (return value properties, heap changes)
- [ ] #4 Human review workflow: AI proposes, human edits, Lean checks
- [ ] #5 Tested on 5+ functions from the scale test module
<!-- AC:END -->
