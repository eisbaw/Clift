---
id: TASK-0243
title: 'Figure: Layered delegation architecture diagram'
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
TikZ diagram showing the human-AI collaboration architecture: Human Director → Primary Agent (Claude Opus 4.6, 1M context) → Sub-agents / Prover persona / Model race skill. Lean 4 kernel as the verification oracle at the bottom. Backlog system as external memory on the side.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 TikZ code in paper/figures/delegation.tex compiles without errors
- [ ] #2 Figure included in clift.tex in Section 4 (AI-Driven Development)
- [ ] #3 PDF page containing figure exported to JPG at 150dpi
- [ ] #4 Visual review by Claude confirms: all layers visible, arrows show delegation flow, Lean kernel oracle prominent, readable labels
- [ ] #5 Iterate TikZ until raster matches intent
<!-- AC:END -->
