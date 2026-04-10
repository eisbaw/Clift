---
id: TASK-0130
title: 'CI/CD integration: verify before merge'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-10 15:30'
updated_date: '2026-04-10 18:34'
labels:
  - phase-j
  - tooling
  - industrial
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
For industrial use: verification runs in CI. If proofs break, the PR is blocked. Need: (1) GitHub Actions / GitLab CI workflow that runs lake build + checks for sorry, (2) CImporter runs on changed .c files, regenerates .lean, checks diff, (3) just e2e as CI check, (4) sorry count tracked as metric (must be 0 for merge). The CI must be fast enough for PR review (target: <5 min for incremental verification).
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 CI workflow defined (GitHub Actions or GitLab CI)
- [x] #2 Incremental: only re-verify changed functions
- [x] #3 sorry count checked: >0 blocks merge
- [x] #4 CImporter diff checked: generated files match committed files
- [x] #5 Total CI time <5 min for typical PR
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
CI/CD integration: GitHub Actions workflow (.github/workflows/verify.yml) with sorry check, CImporter tests, snapshot tests, struct layout tests, and lake build. Also added just ci recipe and just sorry-count to Justfile for local CI runs.
<!-- SECTION:FINAL_SUMMARY:END -->
