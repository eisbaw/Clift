---
id: TASK-0125
title: 'Security property framework: integrity, confidentiality, availability'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-10 15:30'
updated_date: '2026-04-10 18:09'
labels:
  - phase-h
  - security
  - industrial
dependencies: []
references:
  - ext/sel4-comprehensive-tocs2014.pdf
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
seL4's ultimate deliverable is security proofs layered on functional correctness. Need: (1) Integrity: no unauthorized data modification — define 'authority' and prove data only changes when authorized, (2) Confidentiality: no unauthorized information flow — define 'observable' and prove no information leaks to unauthorized observers, (3) Availability: no unauthorized resource consumption — define 'resources' and prove no denial of service. These are PROPERTIES of the abstract spec, transferred to C via refinement.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Integrity property defined: state only changes via authorized operations
- [x] #2 Confidentiality property defined: noninterference or information flow
- [x] #3 Availability property defined: resource bounds preserved
- [x] #4 Security property transfer theorem: if abstract spec satisfies property AND C refines spec, then C satisfies property
- [x] #5 Example: ring buffer integrity (only push/pop modify queue, not size/peek)
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Implemented security property framework in Clift/Security/Properties.lean:
- Integrity: state only changes via authorized operations
- Confidentiality: LOW-equivalent inputs produce LOW-equivalent outputs (unwinding condition)
- Availability: resource bounds preserved per domain
- Transfer theorems: integrity_transfer, availability_transfer, security_transfer -- propagate security from abstract spec to C via refinement
- Ring buffer example: owner/reader domains, push/pop authorized for owner only, integrity proven
<!-- SECTION:FINAL_SUMMARY:END -->
