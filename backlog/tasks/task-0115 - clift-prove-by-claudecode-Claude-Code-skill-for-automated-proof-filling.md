---
id: TASK-0115
title: 'clift-prove-by-claudecode: Claude Code skill for automated proof filling'
status: To Do
assignee: []
created_date: '2026-04-10 15:29'
updated_date: '2026-04-10 16:41'
labels:
  - phase-f
  - ai
  - critical-path
  - industrial
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Build a Claude Code skill (not a standalone script) that automates proof filling. The skill is invoked as a slash command within Claude Code sessions and is portable across LLM backends.

Workflow:
1. User runs /clift-prove <file.lean> (or /clift-prove-all for entire project)
2. The skill scans the file for sorry markers
3. For each sorry: extracts goal state via Lean LSP/server
4. Constructs prompt with: goal + hypotheses + relevant definitions + similar proven lemmas from ProofIndex
5. Claude (or whatever LLM backs Claude Code) generates tactic proof
6. Skill writes tactic into .lean file replacing sorry
7. Runs lake build to kernel-check
8. If error: feeds error + goal state back for retry (up to 3x)
9. Reports: N/M sorries eliminated, K failed (with reasons)

The external script is called clift-prove-by-claudecode and wraps this as a CLI tool that can also be used outside Claude Code sessions (calls claude-code CLI in non-interactive mode).

Key design: the skill is LLM-agnostic at the prompt layer. The prompt construction (goal extraction, context selection, similar-proof retrieval) is the same regardless of which model generates the tactic. Only the API call differs. This means it works with Claude, GPT, DeepSeek-Prover, or any future model.

The Lean kernel is the ONLY trust anchor. The LLM is an untrusted oracle — its output is always kernel-checked before acceptance.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Goal extraction: scan .lean files for sorry, capture goal state
- [ ] #2 Prompt construction: goal + hypotheses + relevant lemmas + function defs
- [ ] #3 Response parsing: extract tactic block from Claude response
- [ ] #4 Apply-and-check loop: apply tactic, check result, retry on failure
- [ ] #5 Tested: 10 proof obligations from ring buffer, 8+ closed automatically
- [ ] #6 End-to-end: file with sorry -> run engine -> file without sorry
- [ ] #7 Claude Code skill defined as /clift-prove slash command
- [ ] #8 Goal extraction from sorry markers via Lean server
- [ ] #9 Prompt construction: goal + context + similar proofs from ProofIndex
- [ ] #10 Apply-check-retry loop (up to 3 retries with error feedback)
- [ ] #11 clift-prove-by-claudecode CLI wrapper for non-interactive use
- [ ] #12 Tested: 10 proof obligations from ring buffer, 8+ closed automatically
- [ ] #13 LLM-agnostic: prompt layer separated from model-specific API call
- [ ] #14 All accepted proofs kernel-checked (zero trust in LLM output)
<!-- AC:END -->
