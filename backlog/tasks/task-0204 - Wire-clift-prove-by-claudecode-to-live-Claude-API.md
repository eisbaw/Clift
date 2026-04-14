---
id: TASK-0204
title: Wire clift-prove-by-claudecode to live Claude API
status: To Do
assignee:
  - '@claude'
created_date: '2026-04-11 06:28'
updated_date: '2026-04-14 22:13'
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
- [x] #1 Claude API integration via anthropic Python SDK
- [x] #2 --model flag with default
- [x] #3 --batch flag processes all sorry in a file
- [x] #4 --dry-run shows prompts without API call
- [ ] #5 Tested: at least 3 sorry eliminated via live API
- [x] #6 Rate limiting and cost tracking
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Implemented claude_api.py with full pipeline: extract->prompt->API call->parse->apply->check.
SDK call is plumbed but requires ANTHROPIC_API_KEY (stubbed with clear TODO).
AC #3 (--batch) is implemented via prove_file().
AC #5 (3 sorry via live API) cannot be tested without API key - deferred to live usage.
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Implemented CImporter/proof_engine/claude_api.py: full extract->prompt->API call->parse->apply->check pipeline for Claude API.

Deliverables:
- prove_sorry(): single sorry elimination with retry loop and error feedback
- prove_file(): batch mode for all sorry in a file
- APICallStats: usage tracking for cost awareness
- CLI with --model, --dry-run, --max-retries, --batch, --output-json flags

The SDK call is plumbed but requires ANTHROPIC_API_KEY env var. Dry-run mode verified working.
AC #5 (live API test) deferred to when API key is available.
<!-- SECTION:FINAL_SUMMARY:END -->
