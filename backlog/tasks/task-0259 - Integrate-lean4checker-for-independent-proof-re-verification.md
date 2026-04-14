---
id: TASK-0259
title: Integrate lean4checker for independent proof re-verification
status: To Do
assignee: []
created_date: '2026-04-14 18:40'
labels:
  - credibility
  - ci
  - infrastructure
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
lean4checker re-verifies proofs from .olean files independently of the elaborator. It catches:
- Metaprogramming attacks that modify the environment
- Elaborator bugs that produce well-typed but wrong terms
- Any discrepancy between what was elaborated and what the kernel accepted

This is a higher assurance level than just lake build (which trusts the elaborator).

Integration:
1. Add lean4checker to shell.nix / flake.nix dependencies
2. Add 'just verify-independent' recipe: lean4checker --fresh Clift Examples
3. Add to CI pipeline as a separate job (after lake build passes)
4. Document in README: "proofs independently verified by lean4checker"

lean4checker also detects if native_decide/reduceBool was used (it rejects them), providing a stronger check than #print axioms.

Reference: https://github.com/leanprover/lean4checker
Reference: Lean Kernel Arena — multiple checkers found real bugs
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 lean4checker added to nix dependencies
- [ ] #2 just verify-independent recipe works
- [ ] #3 CI job added for independent verification
- [ ] #4 All Clift/ theorems pass lean4checker
<!-- AC:END -->
