---
id: TASK-0278
title: 'Paper: improve density — remove duplicates and recover space'
status: Done
assignee: []
created_date: '2026-04-15 07:29'
updated_date: '2026-04-15 07:45'
labels:
  - paper
  - density
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Density reviewer found ~48 recoverable lines: (1) codebase-composition figure duplicates proof metrics table — remove figure. (2) Two worked examples (swap figure + rb_push prose) — keep one. (3) Backward simulation explained twice. (4) Memory model limitations stated twice. (5) CImporter trust in 3 places. (6) Radar figure referenced/summarized 3 times. (7) Thin reproducibility paragraph restated in conclusion.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Remove codebase-composition figure (data is in table)
- [x] #2 Keep one worked example, remove duplicate
- [x] #3 Each concept explained once, referenced elsewhere
- [x] #4 Merge thin Discovery-Driven subsection into parent
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Removed codebase-composition figure (data in table). Removed swap worked-example figure (keep rb_push). Merged Discovery-Driven into paragraph. Trimmed reproducibility paragraph.
<!-- SECTION:FINAL_SUMMARY:END -->
