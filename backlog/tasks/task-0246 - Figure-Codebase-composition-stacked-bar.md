---
id: TASK-0246
title: 'Figure: Codebase composition (stacked bar)'
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
TikZ stacked bar or pie chart showing the 49K LOC breakdown: Library/Clift (13.4K), Proofs/Examples (18.7K), Generated (17.4K), Python/CImporter (5K). Shows how much of the codebase is proof vs infrastructure vs generated.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 TikZ code in paper/figures/codebase-composition.tex compiles without errors
- [ ] #2 Figure included in clift.tex in Section 5 (Evaluation)
- [ ] #3 PDF page containing figure exported to JPG at 150dpi
- [ ] #4 Visual review by Claude confirms: segments clearly labeled with LOC counts, colors distinguishable, legend present, fits column width
- [ ] #5 Iterate TikZ until raster matches intent
<!-- AC:END -->
