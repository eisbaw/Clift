---
id: TASK-0215
title: 'Continuous verification: nightly proof rebuild and sorry tracking'
status: To Do
assignee: []
created_date: '2026-04-11 06:29'
labels:
  - maturity
  - infrastructure
  - ci
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Set up a cron job or CI schedule that rebuilds the entire project nightly, counts sorry, tracks over time, alerts on regression (sorry count increases). This is how seL4 maintains proof quality over years. Plot sorry count over time as a project health metric.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Nightly build job defined (cron or CI scheduled workflow)
- [ ] #2 Sorry count tracked and stored per build
- [ ] #3 Alert on sorry count increase
- [ ] #4 Dashboard or log showing sorry count over time
<!-- AC:END -->
