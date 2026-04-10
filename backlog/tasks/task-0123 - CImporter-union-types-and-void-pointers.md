---
id: TASK-0123
title: 'CImporter: union types and void pointers'
status: To Do
assignee: []
created_date: '2026-04-10 15:29'
labels:
  - phase-g
  - cimporter
  - memory-model
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Embedded C uses unions for type punning (register overlays, protocol parsing) and void* for generic pointers. Need: (1) unions modeled as overlapping memory regions (same base address, different CType interpretations), (2) void* modeled as untyped pointer (Ptr Unit or Ptr Opaque), (3) casting void* to typed pointer emits guard that memory is actually that type. These are inherently unsafe C features — the verification obligations are correspondingly heavy.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Union declarations parsed
- [ ] #2 Union field access emits read at base address with field's CType
- [ ] #3 void* type supported (untyped pointer)
- [ ] #4 Cast from void* to Ptr α emits type-safety guard
- [ ] #5 Test: union-based register overlay
<!-- AC:END -->
