---
id: TASK-0245
title: 'Figure: Clift vs AutoCorres2 radar chart'
status: To Do
assignee: []
created_date: '2026-04-13 11:24'
labels:
  - paper
  - figure
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
TikZ radar/spider chart comparing Clift vs AutoCorres2 across 6 axes: maturity, AI compatibility, type theory expressiveness, automation level, LOC verified, memory model completeness. Visually shows trade-offs between the two approaches.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 TikZ code in paper/figures/radar-comparison.tex compiles without errors
- [ ] #2 Figure included in clift.tex in Section 5 (Evaluation)
- [ ] #3 PDF page containing figure exported to JPG at 150dpi
- [ ] #4 Visual review by Claude confirms: both polygons visible with distinct colors, all 6 axes labeled, legend distinguishes Clift from AutoCorres2, readable at column width
- [ ] #5 Iterate TikZ until raster matches intent
<!-- AC:END -->
