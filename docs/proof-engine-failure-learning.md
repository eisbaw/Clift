# Proof Engine: Learning from Failures to Improve Retry Prompts

Task 0209: Design specification for failure analysis and retry prompt
construction in the proof engine.

## Problem

When Claude's generated proof fails, the Lean error message contains
structured information about what went wrong. Currently, retries use
the same prompt with minor variations. By analyzing the failure and
feeding it back, we can guide Claude toward a correct proof.

## Error Categories

### 1. Unknown Identifier
```
error: unknown identifier 'hoare_guard_modify'
```
**Analysis**: Claude hallucinated a lemma name.
**Retry guidance**: "The lemma `hoare_guard_modify` does not exist.
Available lemmas with similar names: `L1_hoare_guard`, `L1_hoare_modify`,
`L1_guard_modify_result`. Use one of these instead."

### 2. Type Mismatch
```
error: type mismatch
  h_mt.1
has type A but is expected to have type B
```
**Analysis**: Wrong lemma applied, or arguments in wrong order.
**Retry guidance**: Include both the expected type and actual type.
Suggest: "The argument has type `A` but needs type `B`. Check if
you need to rewrite or convert the hypothesis first."

### 3. Unsolved Goals
```
error: unsolved goals
  s : ProgramState
  ⊢ (hVal s.globals.rawHeap s.locals.rb).count = 0
```
**Analysis**: Proof is incomplete. The remaining goal shows what's missing.
**Retry guidance**: Include the unsolved goal state. Suggest tactics:
"The remaining goal is `⊢ P`. Consider using `exact h`, `assumption`,
`simp`, or `omega` to close it."

### 4. Tactic Failed
```
error: 'simp' made no progress
error: 'omega' could not prove the goal
```
**Analysis**: Wrong tactic for this goal shape.
**Retry guidance**: "The tactic `simp` made no progress on goal `⊢ P`.
The goal may need `unfold`, `rw`, or manual case analysis instead."

### 5. Timeout / Heartbeat Exceeded
```
error: (deterministic) timeout at 'elaboration'
```
**Analysis**: Proof term too large or too many unfoldings.
**Retry guidance**: "The proof timed out. Use `attribute [local irreducible]`
to prevent deep unfolding. Use helper lemmas instead of inline proofs."

## Retry Prompt Structure

```
## Previous Attempt

### Goal
{original_goal}

### Attempted Proof
{failed_proof_text}

### Error
{lean_error_message}

### Error Analysis
{structured_analysis}

### What to Try Instead
{specific_suggestions}

## Instructions
Generate a new proof that avoids the error above.
Do not repeat the same approach.
```

## Error Parsing Implementation

1. Parse Lean error output into structured form:
   - Error type (unknown_id | type_mismatch | unsolved | tactic_failed | timeout)
   - Error location (line, column)
   - Error context (goal state, hypothesis names)
   - Error details (expected type, actual type, remaining goals)

2. Pattern match on error type to generate analysis

3. Query ProofIndex for alternative approaches when the first approach fails

## Retry Strategy

- Retry 1: Same approach with error correction (fix the specific error)
- Retry 2: Different approach (different tactic strategy from ProofIndex)
- Retry 3: Simplified goal (weaken postcondition, try `sorry`-free subgoals)

## Metrics

- Track: error type distribution across all proof attempts
- Track: retry success rate by error type
- Target: 30% additional sorry elimination from retries (over first-attempt)

## Limitations

- Error messages from Lean can be verbose and hard to parse automatically
- Some errors indicate fundamental proof strategy problems, not tactical errors
- Hallucinated lemma names require access to the actual lemma database
- Timeout errors may indicate the proof approach is wrong, not just slow
