---
id: TASK-0241
title: 'Figure: Pipeline diagram (5-stage lifting flow)'
status: To Do
assignee: []
created_date: '2026-04-13 11:23'
labels:
  - paper
  - figure
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
TikZ figure showing the Clift 5-stage lifting pipeline: C source → CSimpl → L1 (monadic) → L2 (local extract) → L3 (type strengthen) → L4 (heap lift) → L5 (word abstract) → User proofs. Show corres arrows between stages, label each transform and its effect. This is the central architectural contribution of the paper.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 TikZ code in paper/figures/pipeline.tex compiles without errors
- [ ] #2 Figure included in clift.tex in Section 3 (Architecture)
- [ ] #3 PDF page containing figure exported to JPG at 150dpi
- [ ] #4 Visual review by Claude confirms: all 5 stages labeled, corres arrows visible, readable at column width, no overlapping text
- [ ] #5 Iterate TikZ until raster matches intent
<!-- AC:END -->
