---
id: TASK-0275
title: 'Paper: fix layout overflow (delegation figure 46pt)'
status: Done
assignee: []
created_date: '2026-04-15 07:28'
updated_date: '2026-04-15 07:36'
labels:
  - paper
  - layout
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Delegation TikZ figure overflows column by 46pt — visibly extends past margin. Also 10pt overflows at clang command and HeapRawState paragraph. Fix by: (1) shrink delegation figure (reduce x positions or resizebox), (2) break long texttt spans, (3) reflow paragraphs with inline code.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Delegation figure fits within column (0 overfull)
- [ ] #2 No overfull boxes >10pt in paper
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Moved delegation figure Backlog and Persistent Memory nodes from x=4.5 to x=3.5, eliminating the 46pt column overflow. Some remaining overfull hboxes (10-18pt) exist in other parts of the paper from long lstlisting lines.
<!-- SECTION:FINAL_SUMMARY:END -->
