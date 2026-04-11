---
id: TASK-0215
title: 'Continuous verification: nightly proof rebuild and sorry tracking'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-11 06:29'
updated_date: '2026-04-11 07:26'
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
- [x] #1 Nightly build job defined (cron or CI scheduled workflow)
- [x] #2 Sorry count tracked and stored per build
- [x] #3 Alert on sorry count increase
- [x] #4 Dashboard or log showing sorry count over time
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Added schedule trigger to verify.yml (nightly at 03:00 UTC).
Added sorry count tracking step to CI.
Added just nightly recipe.
Initialized metrics/sorry-count.log.
Alert condition: sorry count > previous.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Added nightly verification infrastructure.

Changes:
- verify.yml: added schedule trigger (nightly 03:00 UTC) + sorry count tracking step + regression alert
- Justfile: added just nightly recipe (full build + sorry count + alert)
- metrics/sorry-count.log: initialized with current count

Sorry count tracked per build with timestamp and commit hash.
Alert fires when sorry count increases vs previous entry.
<!-- SECTION:FINAL_SUMMARY:END -->
