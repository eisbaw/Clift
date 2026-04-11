# Proof Repair Automation: When C Changes, Auto-Fix Broken Proofs

Task 0217: Design document for the proof repair pipeline.

## Problem

When a C source file changes (bug fix, refactor, feature addition), the
generated Lean code changes, and existing proofs may break. In seL4,
proof maintenance after kernel changes consumed person-months. Automated
proof repair could reduce this to minutes.

## Pipeline Overview

```
C file changed
    |
    v
CImporter regenerates Generated/*.lean
    |
    v
`lake build` detects broken proofs
    |
    v
Error parser extracts broken theorem names + new goal states
    |
    v
For each broken proof:
  1. Retrieve the OLD proof text
  2. Extract the NEW goal state from the error
  3. Diff the old goal vs new goal to identify what changed
  4. Feed (old proof + new goal + diff analysis) to Claude
  5. Claude generates repaired proof
  6. Validate with `lake build`
  7. If fails, retry with error feedback (task 0209 pattern)
    |
    v
Report: which proofs repaired, which need manual attention
```

## Change Categories

### 1. Field Rename
C struct field renamed (e.g., `count` -> `num_elements`).
- Effect: All references to the field in proofs break
- Repair: Textual substitution in proof + spec
- Confidence: Very high (mechanical)

### 2. Field Addition
New field added to a struct.
- Effect: Struct layout changes, projection lemmas may break
- Repair: Regenerate roundtrip proofs, adjust offsets
- Confidence: High (mostly mechanical)

### 3. Logic Change
Function body logic changed (e.g., new bounds check added).
- Effect: L1 body changes, validHoare proofs may need new cases
- Repair: Claude generates new proof with old proof as guide
- Confidence: Medium (depends on change magnitude)

### 4. New Function
New function added to the C module.
- Effect: Need new FuncSpec + validHoare proof
- Repair: Not repair but generation (task 0205 pattern)
- Confidence: Medium

### 5. Function Removal
Function removed from C module.
- Effect: Specs and proofs become dead code
- Repair: Remove corresponding Lean theorems
- Confidence: High (delete only)

## Goal Diff Analysis

Compare old goal state with new goal state:
- **Same structure, different names**: field rename, apply substitution
- **Same structure, additional conjuncts**: new conditions added, extend proof
- **Different structure**: significant logic change, re-prove from scratch
- **Subset of original**: logic simplified, proof should be simpler

## Repair Prompt Template

```
## Context
The C source for `{module}` was modified. The proof `{theorem_name}`
no longer compiles.

## Old Proof (worked before the change)
{old_proof_text}

## New Goal State (from the error)
{new_goal_state}

## What Changed
{diff_analysis}

## Instructions
Adapt the old proof to work with the new goal state.
Preserve the proof strategy where possible.
If the change is too large, state what additional lemmas are needed.
```

## Implementation Components

1. **Error Parser**: Extract broken theorem names from `lake build` output
2. **Old Proof Retriever**: Git blame / git diff to find the old proof text
3. **Goal Differ**: Structural comparison of old vs new goal states
4. **Repair Prompter**: Assemble repair prompt with old proof + new goal + diff
5. **Validator**: Run `lake build` on repaired proof, report success/failure
6. **Batch Runner**: Process all broken proofs in dependency order

## Metrics

- **Repair rate**: fraction of broken proofs auto-repaired
- **Repair time**: wall-clock time per repaired proof
- **Manual fallback**: fraction requiring human intervention
- **Regression rate**: repaired proofs that break again on next change

## Estimated Effort

- Error parser: 1 day (extend existing lake build output parsing)
- Goal differ: 2 days (AST-level comparison)
- Repair prompter: 1 day (template + context management)
- Validator + batch: 1 day (extend clift-prove-by-claudecode)
- Testing: 2 days (change ring buffer, verify repair)

## Limitations

- Proof repair is only as good as the diff analysis
- Large logic changes may require re-proving from scratch
- Inter-dependent proofs must be repaired in dependency order
- API cost scales with number of broken proofs
- Cannot repair proofs that were already `sorry`
