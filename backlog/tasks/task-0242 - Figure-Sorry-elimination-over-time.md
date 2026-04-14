---
id: TASK-0242
title: 'Figure: Sorry elimination over time'
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
TikZ line chart showing sorry count vs commit number (or date), from initial ~65 down to 9. Data extracted from git history. Visually conveys the AI grinding through proofs over the 5-day development period.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Data points extracted from git history (sorry count per commit or per day)
- [ ] #2 TikZ code in paper/figures/sorry-timeline.tex compiles without errors
- [ ] #3 Figure included in clift.tex in Section 5 (Evaluation)
- [ ] #4 PDF page containing figure exported to JPG at 150dpi
- [ ] #5 Visual review by Claude confirms: axes labeled, trend clearly visible, data points readable, no clipping
- [ ] #6 Iterate TikZ until raster matches intent
<!-- AC:END -->
