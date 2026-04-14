---
id: TASK-0154
title: 'External review: invite formal methods expert to audit proofs'
status: To Do
assignee: []
created_date: '2026-04-10 18:46'
updated_date: '2026-04-14 22:11'
labels:
  - phase-p
  - community
  - hardening
  - maturity
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The most important maturity step. Find someone who does formal verification professionally (Isabelle, Coq, or Lean) and ask them to: (1) try to break the proofs, (2) review the TCB (CImporter, memory model, Exec rules), (3) assess whether the security properties are meaningful, (4) identify unsound assumptions. Pay for this if needed — it's worth it.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Reviewer identified (formal methods background)
- [ ] #2 Reviewer given access to repo + documentation
- [ ] #3 Review report received
- [ ] #4 All critical findings addressed
- [ ] #5 Review published or summarized in docs/
<!-- AC:END -->
