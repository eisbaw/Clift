---
id: TASK-0256
title: Document CImporter TCB and add differential testing
status: To Do
assignee: []
created_date: '2026-04-14 18:06'
labels:
  - credibility
  - tcb
  - documentation
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The CImporter (Python: clang JSON AST → Lean CSimpl) is in the Trusted Computing Base. If it mistranslates C, all proofs are about the wrong program. This is the same trust model as seL4's StrictC parser.

Current mitigations:
- Snapshot tests (just test-snapshots) — regression on known C files
- Struct layout tests (just test-struct-layout) — gcc sizeof/offsetof agreement
- Integer promotion tests (just test-int-promotion)
- Fuzz testing (just test-fuzz) — 55 random programs

Additional mitigations needed:
1. Differential testing against CompCert Clight parser for shared C subset
2. Edge case tests for integer promotion, implicit conversions, sign extension
3. Document EXACTLY what C semantics the CImporter assumes vs what gcc/clang actually do
4. Add to README/docs: explicit TCB statement with CImporter listed

This is NOT a bug — it's inherent to the approach. But it must be prominently documented so reviewers understand the trust boundary.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 TCB documented in README with CImporter explicitly listed
- [ ] #2 Differential testing against CompCert Clight for 5+ edge cases
- [ ] #3 C semantics assumptions documented (integer promotion, struct layout, etc)
<!-- AC:END -->
