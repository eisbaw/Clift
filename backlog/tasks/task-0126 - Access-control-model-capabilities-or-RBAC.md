---
id: TASK-0126
title: 'Access control model: capabilities or RBAC'
status: To Do
assignee: []
created_date: '2026-04-10 15:30'
labels:
  - phase-h
  - security
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
seL4 uses a capability-based access control model. For an industrial Clift tool, we need a general access control framework. Define: (1) subjects (threads/processes), (2) objects (memory regions, devices, queues), (3) permissions (read, write, execute, send, receive), (4) access policy (which subjects can perform which operations on which objects). Prove: the C implementation enforces the policy.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Subject, Object, Permission types defined
- [ ] #2 AccessPolicy: Subject -> Object -> Set Permission
- [ ] #3 policy_enforced theorem: all C operations check permissions
- [ ] #4 Example: two-partition system where partition A can't read partition B's data
<!-- AC:END -->
