---
id: TASK-0247
title: 'Figure: Trust boundary diagram'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-13 11:24'
updated_date: '2026-04-15 06:02'
labels:
  - paper
  - figure
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
TikZ diagram showing what is in the Trusted Computing Base (CImporter Python script, clang, Lean 4 kernel) vs what is verified by proofs (Clift library, lifting stages, refinement proofs, user proofs). Important for a verification paper to be explicit about trust assumptions.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 TikZ code in paper/figures/trust-boundary.tex compiles without errors
- [x] #2 Figure included in clift.tex in Section 3 (Architecture)
- [ ] #3 PDF page containing figure exported to JPG at 150dpi
- [ ] #4 Visual review by Claude confirms: TCB region visually distinct (e.g. red/shaded), verified region clearly separated, all components labeled, readable
- [ ] #5 Iterate TikZ until raster matches intent
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
TikZ figure created in paper/figures/, included in clift.tex, compiles and renders correctly in PDF.
<!-- SECTION:FINAL_SUMMARY:END -->
