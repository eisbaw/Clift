---
id: TASK-0268
title: 'Fix just sorry-count: grep reports ~42 but actual is 17'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-14 20:57'
updated_date: '2026-04-14 22:08'
labels:
  - tooling
  - correctness
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The just sorry-count recipe uses grep with basic comment filtering (grep -v "^.*:.*--") which misses Lean block comments (/-\! ... -/), sorryAx references in linter code, and docstring mentions of sorry. The Python audit (tools/lint/audit.py) gives the correct count of 17. Either fix the grep filters or delegate to the Python audit.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 just sorry-count output matches python3 tools/lint/audit.py sorry count
- [x] #2 metrics/sorry-count.log records the correct number
<!-- AC:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Added sorry-count and nightly recipes to Justfile that delegate to python3 tools/lint/audit.py instead of broken grep. Fixed metrics/sorry-count.log to record the correct count (17, not 82).
<!-- SECTION:FINAL_SUMMARY:END -->
