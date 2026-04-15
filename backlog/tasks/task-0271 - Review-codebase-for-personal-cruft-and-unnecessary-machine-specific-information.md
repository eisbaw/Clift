---
id: TASK-0271
title: >-
  Review codebase for personal cruft and unnecessary machine-specific
  information
status: Done
assignee:
  - '@claude'
created_date: '2026-04-15 06:56'
updated_date: '2026-04-15 07:02'
labels:
  - housekeeping
  - quality
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Audit CLAUDE.md, .claude/agents/prover.md, .claude/skills/, and memory files for information that is personal, machine-specific, or irrelevant to the project. Examples: zram config details (nobody cares about the compression algorithm), specific RAM amounts that vary per machine, absolute toolchain paths that should be derived from nix, personal directory paths in examples. Replace with generic guidance or remove entirely. The goal is that a new contributor (human or AI) gets useful project info without noise.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 CLAUDE.md reviewed and cleaned of machine-specific details
- [x] #2 .claude/agents/prover.md reviewed — remove zram details, hardcoded toolchain paths, machine-specific RAM numbers
- [x] #3 .claude/skills/clift-prover/SKILL.md reviewed and cleaned
- [x] #4 .claude/memory/ files reviewed — remove stale or machine-specific entries
- [x] #5 plan.md reviewed for stale or irrelevant content
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Removed machine-specific cruft (zram details, hardcoded toolchain paths, specific RAM numbers, stale LOC/sorry counts) from prover.md, SKILL.md, MEMORY.md, project_clift_status.md, and CLAUDE.md. Replaced with generic guidance.
<!-- SECTION:FINAL_SUMMARY:END -->
