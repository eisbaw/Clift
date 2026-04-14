---
id: TASK-0150
title: 'Lean 4 version upgrade test: upgrade toolchain, fix breakage'
status: To Do
assignee: []
created_date: '2026-04-10 18:46'
updated_date: '2026-04-14 22:11'
labels:
  - phase-o
  - maintenance
  - infrastructure
dependencies: []
priority: low
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
We're on leanprover/lean4:v4.30.0-rc1. Lean 4 updates frequently and sometimes breaks code. Test: upgrade to latest stable, fix all breakage, document what broke and why. This validates long-term viability. seL4 pinned to specific Isabelle versions and updated deliberately.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Upgraded to latest stable Lean 4
- [ ] #2 All breakage fixed (or documented as blocking)
- [ ] #3 Breaking changes categorized: syntax, tactic, kernel, API
- [ ] #4 Upgrade guide written for future upgrades
<!-- AC:END -->
