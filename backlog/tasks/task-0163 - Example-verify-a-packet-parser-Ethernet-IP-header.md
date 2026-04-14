---
id: TASK-0163
title: 'Example: verify a packet parser (Ethernet/IP header)'
status: To Do
assignee: []
created_date: '2026-04-10 18:47'
updated_date: '2026-04-14 22:12'
labels:
  - phase-n
  - examples
  - network
  - security
dependencies: []
priority: low
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Network packet parsing is security-critical — malformed packets from the network must not cause UB. Parse Ethernet + IPv4 headers (~200 LOC): validate frame, extract fields, check checksums. Prove: well-formed packets parsed correctly, malformed packets rejected, no buffer overrun on any input. Exercises: pointer arithmetic, bitwise field extraction, bounds checking.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Packet parser C source (200+ LOC)
- [ ] #2 Spec: Ethernet/IP header as Lean structure
- [ ] #3 Well-formed packets: fields extracted correctly
- [ ] #4 Malformed packets: rejected without UB
- [ ] #5 Buffer overrun freedom for all inputs
<!-- AC:END -->
