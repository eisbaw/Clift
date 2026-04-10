---
id: TASK-0126
title: 'Access control model: capabilities or RBAC'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-10 15:30'
updated_date: '2026-04-10 18:10'
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
- [x] #1 Subject, Object, Permission types defined
- [x] #2 AccessPolicy: Subject -> Object -> Set Permission
- [x] #3 policy_enforced theorem: all C operations check permissions
- [x] #4 Example: two-partition system where partition A can't read partition B's data
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Implemented access control model in Clift/Security/AccessControl.lean:
- Subject, Object, Permission types with AccessPolicy record
- policy_enforced via PolicyEnforcement structure connecting to AbstractSpec
- operationPermitted and policyDeniesUnauthorized definitions
- Two-partition ring buffer example with proven isolation (partA_doesnt_touch_B, partB_doesnt_touch_A)
- All theorems proven without sorry
<!-- SECTION:FINAL_SUMMARY:END -->
