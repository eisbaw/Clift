---
id: TASK-0176
title: 'Capability system verification: unforgeability, delegation, revocation'
status: To Do
assignee: []
created_date: '2026-04-10 18:53'
labels:
  - phase-n
  - seL4-parity
  - security
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
seL4's access control is capability-based with specific properties: capabilities are unforgeable (cannot be manufactured from raw data), can be delegated (derived capabilities), and can be revoked (destroying all derived capabilities). TASK-0126 (Done) built a generic AccessPolicy framework but does not capture capability-specific semantics. Need: (1) Capability type with derivation tree structure, (2) Unforgeability theorem: no operation creates a capability without deriving from an existing one, (3) Delegation: derived capabilities have subset permissions, (4) Revocation: revoking a capability invalidates all descendants, (5) Example: capability-protected ring buffer where access requires holding the right cap. Without capability-specific proofs, the security model is just access-control-in-name-only.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Capability type with derivation tree
- [ ] #2 Unforgeability theorem proven
- [ ] #3 Delegation: derived caps have subset permissions proven
- [ ] #4 Revocation: invalidates descendants proven
- [ ] #5 Example: capability-protected resource
<!-- AC:END -->
