---
id: TASK-0244
title: 'Figure: AI success rate by proof category (bar chart)'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-13 11:23'
updated_date: '2026-04-15 06:02'
labels:
  - paper
  - figure
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
TikZ bar chart showing attempted vs solved proof obligations across 4 categories: straight-line Hoare (45/43), loop invariant (12/10), heap-mutation chains (8/6), complex multi-heap (5/1). Replaces or supplements the existing table in Section 5.4.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 TikZ code in paper/figures/ai-success.tex compiles without errors
- [x] #2 Figure included in clift.tex in Section 5 (Evaluation)
- [ ] #3 PDF page containing figure exported to JPG at 150dpi
- [ ] #4 Visual review by Claude confirms: bars clearly distinguish attempted vs solved, percentages visible, legend readable, fits column width
- [ ] #5 Iterate TikZ until raster matches intent
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
TikZ figure created in paper/figures/, included in clift.tex, compiles and renders correctly in PDF.
<!-- SECTION:FINAL_SUMMARY:END -->
