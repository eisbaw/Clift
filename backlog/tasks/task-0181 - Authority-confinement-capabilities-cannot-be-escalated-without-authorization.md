---
id: TASK-0181
title: 'Authority confinement: capabilities cannot be escalated without authorization'
status: Done
assignee: []
created_date: '2026-04-10 18:54'
updated_date: '2026-04-10 23:39'
labels:
  - phase-n
  - seL4-parity
  - security
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
seL4 proved authority confinement: no operation can create or escalate authority beyond what the caller already holds. This is distinct from noninterference (information flow) and access control enforcement (policy checking). Authority confinement says: even a malicious user cannot gain more authority than they were given. Need: (1) Define authority ordering (cap A >= cap B means A has at least B's permissions), (2) Monotonicity theorem: no operation increases authority beyond the caller's, (3) No-leak theorem: authority is not transferred without explicit Grant permission, (4) Compose with access control framework from TASK-0126. This is the property that makes capabilities a security mechanism, not just an access control mechanism.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Authority ordering defined on capabilities
- [ ] #2 Monotonicity: no operation escalates authority
- [ ] #3 No-leak: authority not transferred without Grant
- [ ] #4 Composed with AccessPolicy framework
<!-- AC:END -->
