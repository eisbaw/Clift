---
id: TASK-0269
title: 'Paper: add Future Work section on mvcgen/SpecM architecture pivot'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-14 21:35'
updated_date: '2026-04-14 23:14'
labels:
  - paper
dependencies: []
documentation:
  - >-
    backlog/docs/doc-0001 -
    Sebastian-Ullrich-feedback-Std.Do.Triple-mvcgen-skip-CSimpl.md
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Sebastian Graf (Lean FRO) suggested replacing custom validHoare with Std.Do.Triple + mvcgen, and skipping CSimpl by emitting monadic SpecM code directly from CImporter. His LeanCorres PoC (github.com/sgraf812/LeanCorres) validates the approach. This should be captured as Future Work in the paper, not as current architecture.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Future Work section describes the mvcgen/SpecM pivot
- [x] #2 References LeanCorres PoC and Sebastian Graf feedback
- [x] #3 Explains tradeoffs: complexity reduction vs TCB expansion
- [x] #4 Notes that while loops and nondeterminism are supported by SpecM (not a blocker)
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Added subsection "Architecture Pivot: mvcgen and SpecM" to the Limitations and Future Work section (Section 6). Added LeanCorres bib entry to references.bib. Paper builds cleanly with lualatex (6 pages, no errors).
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Added a Future Work subsection to the Clift paper covering the mvcgen/SpecM architecture pivot suggested by Sebastian Graf (Lean FRO).

Changes:
- paper/clift.tex: Added subsection 6.1 "Architecture Pivot: mvcgen and SpecM" with four paragraphs covering (1) replacing custom Hoare logic with Std.Do.Triple + mvcgen, (2) skipping CSimpl to emit monadic SpecM code directly, (3) TCB expansion tradeoffs, and (4) feasibility evidence from LeanCorres PoC.
- paper/references.bib: Added leancorres2026 entry for Sebastian Graf's LeanCorres repository.\n\nPaper builds cleanly (6 pages, no LaTeX errors or undefined references).
<!-- SECTION:FINAL_SUMMARY:END -->
