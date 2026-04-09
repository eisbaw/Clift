---
id: TASK-0077
title: 'CImporter: support for, do-while, switch (desugared)'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-09 19:34'
updated_date: '2026-04-09 20:39'
labels:
  - phase-5
  - cimporter
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The CImporter currently handles if/else and while. Real C uses for loops, do-while, and switch statements heavily. For and do-while can be desugared to while. Switch needs careful handling (fall-through is excluded by StrictC, so each case is independent). Extend the CImporter to handle these.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 for loops desugared to while (init; while(cond) { body; step })
- [x] #2 do-while supported (body; while(cond) { body })
- [x] #3 switch without fall-through mapped to nested if/else
- [x] #4 Tests for each construct
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
CImporter now desugars for, do-while, and switch in ast_parser.py. For: init; while(cond) { body; step }. Do-while: body; while(cond) { body }. Switch: nested if/else (no fall-through per StrictC, each case ends with break). Added ConstantExpr handling for switch case values. Tests: for_loop.c, do_while.c, switch_test.c all import correctly. All generated Lean files compile.
<!-- SECTION:FINAL_SUMMARY:END -->
