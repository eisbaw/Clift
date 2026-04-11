# Proof Engine: Context Window Management for Large Goals

Task 0208: Design specification for intelligent context selection when
proof goals exceed the context window budget.

## Problem

Some validHoare goals have 20+ hypotheses, complex nested types, and deep
struct projections. A single goal can exceed 2K tokens before adding
definitions, similar proofs, and the function body. The Claude API context
window (200K tokens) is large but prompt engineering requires keeping
proof-relevant context concentrated.

## Budget Target

- Total prompt size: <8K tokens per proof attempt
- Goal state: ~2K tokens max
- Relevant definitions: ~2K tokens
- Similar proofs: ~2K tokens
- Instructions + format: ~2K tokens

## Context Selection Strategy

### 1. Hypothesis Ranking by Relevance

Score each hypothesis by how related it is to the goal conclusion:

- **Direct mention** (score 10): hypothesis variable appears in the goal
- **Type overlap** (score 5): hypothesis type shares constructors with goal type
- **Transitive** (score 2): hypothesis mentions a variable that another relevant hypothesis mentions
- **Background** (score 0): hypothesis doesn't connect to the goal

Include top-scored hypotheses up to budget. Always include:
- All hypotheses mentioned in the goal conclusion
- All hypotheses that provide decidability instances for predicates in the goal

### 2. Type Truncation

Large types (HeapRawState, ProgramState) have many fields. When displaying:
- Show only fields referenced in the goal
- Replace unreferenced struct fields with `...`
- Abbreviate deeply nested types: `Ptr (C_rb_node)` instead of full definition

### 3. Definition Selection

Include only definitions directly referenced in the goal:
- The function body being verified (always include)
- FuncSpec pre/post (always include)
- `hVal`, `heapPtrValid`, `heapUpdate` when heap operations involved
- L1 combinators referenced in the body (L1.guard, L1.modify, L1.seq, etc.)

Do NOT include:
- Full struct definitions (unless fields are being projected)
- Unrelated function specs
- Library lemmas (reference by name only)

### 4. Similar Proof Selection (from ProofIndex)

Use the ProofIndex to find proofs with matching patterns:
- Same L1 combinator pattern (e.g., guard-modify-throw-catch-skip)
- Same postcondition shape (conjunction, implication, equality)
- Same proof technique (unfold + apply helper, case split, induction)

Include 1-2 similar proofs, truncated to the key tactic sequence.

## Implementation Plan

1. Parse goal into AST, extract referenced names
2. Score hypotheses, select top-N within budget
3. Truncate types that exceed per-type budget (100 tokens)
4. Query ProofIndex for similar patterns
5. Assemble prompt within total budget
6. If over budget: drop lowest-scored hypotheses first, then truncate similar proofs

## Metrics

- Measure: tokens per prompt, first-attempt success rate
- Compare: full context vs. managed context
- Target: no degradation in success rate with 50% token reduction

## Limitations

- Hypothesis ranking is heuristic; may miss transitive relevance
- Type truncation may hide information needed for the proof
- ProofIndex quality depends on having enough proven examples
- Budget is per-attempt; retries can use different context selections
