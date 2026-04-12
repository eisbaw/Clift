---
id: TASK-0153
title: 'Write a paper: Clift — Lifting C into Lean 4 for Formal Verification'
status: In Progress
assignee:
  - '@claude'
created_date: '2026-04-10 18:46'
updated_date: '2026-04-12 21:59'
labels:
  - phase-p
  - community
  - paper
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Write a scientific paper documenting Clift: a C-to-Lean4 formal verification pipeline, heavily inspired by seL4/AutoCorres2 prior art, and its progress towards proving seL4 in Lean 4.

Key angles:
- This project is 99% AI-made (Claude Opus 4.6 thinking 1M context) with significant human guidance via Claude Code sessions. The paper demonstrates the scale and depth of current AI capabilities using seL4 and AutoCorres2 as cases and grounding. This is non-trivial work.
- Making something useful: the Lean community is large and AI is better at Lean than Isabelle. Clift admits lower adoption costs thanks to AI assistance.
- Target: 5-8 page scientific paper with proper references section and all standard sections expected of a scientific paper.

Claude Code session transcripts for this repo (primary source material for AI collaboration evidence):
- ~/.claude/projects/-home-mpedersen-topics-formal-verification/333b8741-c6a1-4d04-be15-fd90cf326e80.jsonl — backlog audit session
- ~/.claude/projects/-home-mpedersen-topics-formal-verification/7e6e3ae0-9162-45e1-b9f1-c1a599158132.jsonl — project assessment session ("how far are we, is the methodology working?")
- ~/.claude/projects/-home-mpedersen-topics-formal-verification/89261b1f-7ab3-4b38-8c3c-793b8d3139fd.jsonl — Lean 4 slides research session

Existing outline: docs/paper-outline.md
Target venues: CPP, ITP, or PLDI.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Add separate LaTeX devShell environment (nix flake) with LuaTeX and packages needed for beautiful scientific papers
- [ ] #2 Write LaTeX paper (5-8 pages): introduction, background/prior art, Clift architecture, AI-driven methodology, evaluation, related work, conclusion
- [ ] #3 Comparison with seL4/AutoCorres2: what is same, what is different, what is better; Lean vs Isabelle adoption costs
- [ ] #4 Evaluation section: LOC, proof ratio, automation rate, Claude success rate, sorry elimination stats
- [ ] #5 Document AI collaboration: 99% AI-made with human guidance, reference Claude Code session transcripts as evidence
- [ ] #6 Proper references section citing seL4, AutoCorres2, Lean 4, and relevant formal verification literature
- [ ] #7 Generate PDF from LaTeX using LuaTeX
- [ ] #8 Extract each PDF page as raster JPG images and visually inspect; iterate until layout and typography are perfect
- [ ] #9 Final paper ready for venue submission
<!-- AC:END -->
