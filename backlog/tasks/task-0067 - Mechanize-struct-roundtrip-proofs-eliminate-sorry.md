---
id: TASK-0067
title: Mechanize struct roundtrip proofs (eliminate sorry)
status: To Do
assignee: []
created_date: '2026-04-09 17:13'
labels:
  - phase-3c
  - proof
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Generated struct MemType instances (e.g. C_node) use sorry for the fromBytes/toBytes roundtrip proof. These need to be proven mechanically. The proof structure: show each field reads back correctly given the if-then-else dispatch in toBytes, using omega for the byte range conditions.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 C_node.fromBytes_toBytes proven (no sorry)
- [ ] #2 Proof generator handles arbitrary struct shapes
<!-- AC:END -->
