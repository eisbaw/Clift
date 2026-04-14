---
id: TASK-0262
title: Build Python audit tool (tools/lint/audit.py) replacing grep-based just audit
status: To Do
assignee: []
created_date: '2026-04-14 18:49'
labels:
  - tooling
  - audit
  - credibility
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Replace the 80+ line bash/grep-based just audit recipe with a proper Python audit tool.

LOCATION: tools/lint/audit.py

WHY: The grep-based audit is fragile (missed sorry due to indent patterns multiple times), has no AST awareness (can't distinguish sorry in comments vs proofs), and is hard to maintain (each check is a 10-line bash block).

CHECKS TO IMPLEMENT (one function per anti-pattern):

1. sorry_count() — count actual sorry in tactic position (not in comments, not in strings)
   - Parse lines: skip -- comments, skip /- -/ block comments
   - Match: 'sorry' as standalone tactic (after 'by', after ';', as indented line)
   - Report: per-file counts + total

2. hand_written_l1() — detect hand-written L1 bodies
   - Match: 'def l1_' or 'noncomputable def l1_' in Examples/
   - Exclude: 'let l1_' (local bindings), comments

3. wrong_target() — detect proofs against manual/fused bodies
   - Match: 'satisfiedBy.*_manual' or 'satisfiedBy.*_fused'
   - Also detect: satisfiedBy targeting a non-Module.l1_ name

4. tautological_weakening() — detect validHoare_weaken_trivial_post usage
   - Match: 'validHoare_weaken_trivial_post' not in definition or comment

5. circular_specs() — detect specs with result set = property
   - Match: 'results := fun.*∃.*∧' pattern

6. custom_axioms() — detect axiom/constant declarations
   - Match: '^axiom ' or '^constant ' in Clift/ and Examples/

7. sorry_axiom() — run #print axioms and detect sorryAx
   - Parse lake build output for sorryAx mentions
   - Or run lean4checker if available

8. native_decide() — detect native_decide in proof-critical code
   - Match: 'native_decide' not in AI test files or comments

9. csimp_smuggling() — detect @[csimp] usage
   - Match: '@[csimp]' in any file

10. implemented_by() — detect @[implemented_by] usage
    - Match: '@[implemented_by]' in any file

11. unsafe_defs() — detect unsafe definitions
    - Match: '^unsafe ' in Clift/ and Examples/

12. vacuous_preconditions() — detect False in preconditions
    - Match: 'fun _ => False' or 'fun s => False' in pre/precondition context

OUTPUT: Structured report with severity levels (FAIL/WARN/INFO/OK) and JSON option for CI.

INTEGRATION:
- just audit calls tools/lint/audit.py
- CI calls it with --json flag for machine-readable output
- Exit code 0 if no FAIL, 1 if any FAIL

PRIOR TASKS TO REVIEW AND SUBSUME:
- TASK-0232 (Custom Lean 4 linter: flag tautological FuncSpec postconditions) — Python tool handles the grep-level checks, MetaM handles the semantic checks
- TASK-0254 (Replace native_decide) — detection part handled by this tool
- TASK-0257 (@[csimp] detection) — handled by this tool
- TASK-0258 (Vacuous preconditions) — grep-level detection handled here, MetaM for semantic check
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 tools/lint/audit.py implemented with all 12 checks
- [ ] #2 Output matches or exceeds current just audit coverage
- [ ] #3 JSON output mode for CI (--json flag)
- [ ] #4 just audit recipe updated to call audit.py
- [ ] #5 All current grep-based checks pass identically
- [ ] #6 Reviews and subsumes detection parts of TASK-0232, 0254, 0257, 0258
<!-- AC:END -->
