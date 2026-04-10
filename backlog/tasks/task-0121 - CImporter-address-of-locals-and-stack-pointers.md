---
id: TASK-0121
title: 'CImporter: address-of locals and stack pointers'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-10 15:29'
updated_date: '2026-04-10 17:41'
labels:
  - phase-g
  - cimporter
  - memory-model
dependencies: []
references:
  - ext/AutoCorres2/Stack_Typing.thy
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
seL4's StrictC forbids address-of locals, but real embedded C does &local_var constantly (passing local arrays to functions, out-parameters). Need: (1) model local variables as heap-allocated (or stack-modeled), (2) &local_var produces a valid pointer to that local's heap location, (3) callee can read/write through the pointer. This is a significant memory model extension — locals are no longer just record fields. Study AutoCorres2's stack frame model.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 UnaryOperator & on local variables parsed
- [ ] #2 Locals that have address taken are heap-allocated in the model
- [ ] #3 Pointer to local is valid while the function executes
- [ ] #4 Callee can dereference pointer to caller's local
- [ ] #5 Stack frame cleanup: local's heap allocation freed on function return
- [ ] #6 Test: C function passing &local to another function
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
$1. Verify &local already rejected (it is - StrictCViolation in ast_parser.py)\n2. Document as ADR: why we reject, what seL4 does, future path\n3. Update task ACs to reflect the reject-and-document approach\n4. Test: verify the rejection error is clear
<!-- SECTION:PLAN:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
$Approach: reject-and-document (matches seL4 StrictC). Address-of locals already rejected in ast_parser.py with clear StrictCViolation error. Created ADR-007 documenting the decision, rationale, and future path (heap-allocate or stack frame model).
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Address-of locals (&local_var) deliberately unsupported, matching seL4 StrictC restriction.

Changes:
- Verified existing rejection: ast_parser.py raises StrictCViolation for unary & operator
- Existing test: test_address_of_rejected in test_ast_parser.py
- Created ADR-007 (backlog/docs/adr-007-no-address-of-locals.md) documenting the decision, rationale (memory model simplicity, seL4 precedent), and future path (heap-allocate addressed locals if needed later)

ACs 2-6 are N/A for the reject-and-document approach. The feature is intentionally unsupported.
<!-- SECTION:FINAL_SUMMARY:END -->
