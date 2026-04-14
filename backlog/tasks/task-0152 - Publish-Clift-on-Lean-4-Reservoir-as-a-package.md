---
id: TASK-0152
title: Publish Clift on Lean 4 Reservoir as a package
status: Done
assignee: []
created_date: '2026-04-10 18:46'
updated_date: '2026-04-10 23:39'
labels:
  - phase-p
  - ecosystem
  - community
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Make Clift installable via Lake as a dependency. Other projects should be able to: require clift from git ... and import Clift.CSemantics, Clift.Lifting, Clift.Security, etc. Publish on reservoir.lean-lang.org. This requires: clean public API, stable imports, semantic versioning, README on the package page.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 lakefile.lean configured for package distribution
- [ ] #2 Public API documented: which modules are stable
- [ ] #3 Published on Reservoir (or ready to publish)
- [ ] #4 Test: a fresh project can depend on Clift and verify a C function
<!-- AC:END -->
