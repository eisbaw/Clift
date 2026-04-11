---
id: TASK-0204
title: Wire clift-prove-by-claudecode to live Claude API
status: To Do
assignee: []
created_date: '2026-04-11 06:28'
labels:
  - critical-path
  - ai
  - proof-engine
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The proof engine framework exists (extract_goals.py, build_prompt.py, apply_proof.py) but uses a mock LLM. Wire it to the real Claude API via the Anthropic SDK. Add --model flag (default claude-sonnet-4-20250514). Add --batch flag to process all sorry in a file. Add --dry-run to show prompts without calling API. This is the key enabler: once wired, we can batch-process all 57 sorry overnight.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Claude API integration via anthropic Python SDK
- [ ] #2 --model flag with default
- [ ] #3 --batch flag processes all sorry in a file
- [ ] #4 --dry-run shows prompts without API call
- [ ] #5 Tested: at least 3 sorry eliminated via live API
- [ ] #6 Rate limiting and cost tracking
<!-- AC:END -->
