---
id: TASK-0182
title: 'Sorry audit: systematically eliminate all sorry from proven theorems'
status: To Do
assignee: []
created_date: '2026-04-10 18:54'
labels:
  - phase-l
  - soundness
  - critical
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Any 'sorry' in the codebase is an unproven assumption that could hide unsoundness. TASK-0135 tries to prove False (sanity check), and TASK-0144 checks #print axioms, but neither systematically tracks sorry elimination. Need: (1) Run 'grep sorry' across all .lean files, count and categorize, (2) For each sorry: is it in a theorem (dangerous), an example (acceptable temporarily), or a stub (needs implementation)? (3) Track sorry count as a metric -- it should monotonically decrease, (4) Block release milestones on zero sorry in core modules (MonadLib, CSemantics, Lifting). A formal methods reviewer will grep for sorry FIRST -- any remaining sorry in core modules is an immediate credibility hit.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Full sorry inventory: file, line, category (core/example/stub)
- [ ] #2 Zero sorry in MonadLib/
- [ ] #3 Zero sorry in CSemantics/
- [ ] #4 Zero sorry in Lifting/ (excluding examples)
- [ ] #5 Sorry count tracked as CI metric
<!-- AC:END -->
