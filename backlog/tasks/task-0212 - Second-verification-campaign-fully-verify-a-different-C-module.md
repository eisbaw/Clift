---
id: TASK-0212
title: 'Second verification campaign: fully verify a different C module'
status: To Do
assignee:
  - '@claude'
created_date: '2026-04-11 06:29'
updated_date: '2026-04-14 22:11'
labels:
  - verification
  - depth
  - milestone
dependencies:
  - TASK-0211
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
One verified module could be a fluke. Verify a second module end-to-end with zero sorry: pick one of RTOS queue, SHA-256, UART driver, or packet parser. Full pipeline: import, lift, abstract spec, invariants, per-function FuncSpecs, validHoare proofs, refinement theorem. Measure effort and compare with ring buffer. This validates the tool is general, not module-specific.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Second module selected (different domain from ring buffer)
- [ ] #2 All functions have FuncSpecs with full functional correctness postconditions
- [ ] #3 All validHoare proofs complete (zero sorry)
- [ ] #4 Refinement theorem proven
- [ ] #5 Effort measured and compared with ring buffer
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Assessment document written: docs/verification-campaign-second-module.md. Recommends SHA-256 Core as the second verification target (different domain from ring buffer, tests bitwise proof patterns, already imported). Includes function-by-function plan, effort estimate (3-5 days), risk assessment. Not yet executed -- this is a planning task. Execution depends on completing the proof infrastructure from ring buffer verification.
<!-- SECTION:FINAL_SUMMARY:END -->
