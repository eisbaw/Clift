---
id: TASK-0180
title: 'Exception/fault delivery verification: CPU faults routed to user handlers'
status: Done
assignee: []
created_date: '2026-04-10 18:54'
updated_date: '2026-04-10 23:39'
labels:
  - phase-n
  - seL4-parity
  - kernel
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
seL4 verified that CPU exceptions (page faults, undefined instructions, syscall faults) are correctly delivered to user-space fault handlers. This is a critical safety property: if exception delivery is wrong, faults are lost or misrouted. Need: (1) Exception type enumeration (page fault, undefined instruction, etc.), (2) Fault handler dispatch model, (3) Verify: each exception type is routed to the correct handler, (4) Verify: exception state (fault address, error code) is correctly captured, (5) Example: page fault delivery to a user handler. This is distinct from CSimpl's .fault outcome (which models UB) -- this is about modeling and verifying the kernel's exception handling mechanism.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Exception types enumerated
- [ ] #2 Fault handler dispatch model defined
- [ ] #3 Routing correctness proven for at least 2 exception types
- [ ] #4 Exception state (fault addr, error code) correctly captured
<!-- AC:END -->
