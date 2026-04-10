---
id: TASK-0115
title: 'Claude-in-the-loop proof engine: auto-feed goals, apply results, iterate'
status: To Do
assignee: []
created_date: '2026-04-10 15:29'
labels:
  - phase-f
  - ai
  - critical-path
  - industrial
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The missing piece between Claude's 85% success rate and full automation. Build a pipeline: (1) extract sorry/goal states from Lean, (2) format as prompts with context (available lemmas, function defs, types), (3) call Claude API (or file-based for now), (4) parse returned tactic script, (5) apply in Lean, (6) if fails, feed error back for retry (up to 3). This turns Claude from an interactive assistant into an automated proof engine. Study Aeneas's progress tactic and LeanDojo's approach for proof extraction.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Goal extraction: scan .lean files for sorry, capture goal state
- [ ] #2 Prompt construction: goal + hypotheses + relevant lemmas + function defs
- [ ] #3 Response parsing: extract tactic block from Claude response
- [ ] #4 Apply-and-check loop: apply tactic, check result, retry on failure
- [ ] #5 Tested: 10 proof obligations from ring buffer, 8+ closed automatically
- [ ] #6 End-to-end: file with sorry -> run engine -> file without sorry
<!-- AC:END -->
