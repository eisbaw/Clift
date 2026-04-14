---
id: TASK-0248
title: 'Figure: Worked example visual (C → CSimpl → L1 → proof)'
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
TikZ figure showing a side-by-side or sequential transformation of a concrete example (e.g. rb_push or swap): original C code → CSimpl deep embedding → L1 monadic form → Hoare triple proof. Pedagogical figure making the pipeline concrete.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 TikZ code in paper/figures/worked-example.tex compiles without errors
- [ ] #2 Figure included in clift.tex in Section 3 (Architecture)
- [ ] #3 PDF page containing figure exported to JPG at 150dpi
- [ ] #4 Visual review by Claude confirms: all 3-4 stages shown with real code snippets, arrows between stages, transformation labeled, readable font size
- [ ] #5 Iterate TikZ until raster matches intent
<!-- AC:END -->
