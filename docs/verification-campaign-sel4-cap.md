# Third Verification Campaign: seL4 Capability Functions

Task 0213: Assessment of verifying seL4 capability functions.

## Purpose

Demonstrate direct parity with AutoCorres2 for a subset of seL4 kernel
functions. This is the credibility milestone.

## Target: sel4_cap.c

Already imported as Generated/Sel4Cap.lean. Contains 6 functions:
- `capType`: extract capability type from bitfield
- `capPtr`: extract capability pointer from bitfield
- `cap_is_null`: check if capability is null
- `isArchObjectType`: check if cap type is an architecture object
- `lookup_fault_depth_mismatch`: construct a lookup fault
- `cte_insert`: insert a capability table entry

## Current State

- All 6 functions imported and lifted to L1 (L1corres proven)
- FuncSpecs defined for capType, capPtr, cap_is_null (Sel4CapProof.lean)
- 3 validHoare proofs completed (capType, capPtr, cap_is_null)
- 2 sorry remaining (isArchObjectType, lookup_fault_depth_mismatch)
- cte_insert not yet specified (complex heap mutation)

## What Full Verification Means

For each function:
1. **FuncSpec**: Pre/postcondition capturing exact bit-level behavior
2. **validHoare**: L1 body satisfies the spec (kernel-checked)
3. **totalHoare**: No UB for non-loop functions
4. **Functional correctness**: Postcondition specifies exact return value
5. **Comparison with AutoCorres2**: Same function, same spec, compare proof

## Function-by-Function Assessment

### capType (DONE)
- Extracts bits [59:64) from a 64-bit word
- Proof: guard-modify-throw-catch-skip pattern
- ~20 lines of proof
- AutoCorres2 comparison: similar complexity

### capPtr (DONE)
- Extracts bits [0:48) from a 64-bit word
- Same pattern as capType
- ~20 lines of proof

### cap_is_null (DONE)
- Checks if both cap words are zero
- Conditional pattern with two comparisons
- ~30 lines of proof

### isArchObjectType (2 sorry)
- Switch statement over cap type values
- Needs: L1.condition chain reasoning for multi-way branch
- Estimated effort: 0.5 day
- Blocker: need conditional pattern proof helper

### lookup_fault_depth_mismatch (1 sorry)
- Constructs a fault struct from arguments
- Multi-field heap write
- Estimated effort: 0.5 day
- Blocker: heap write projection lemmas

### cte_insert (not started)
- Complex: reads and writes multiple heap objects
- Inter-procedural: may call other functions
- Estimated effort: 2-3 days
- Blocker: heap reasoning for multi-object updates

## Estimated Total Effort

- Complete remaining 2 sorry: 1 day
- Add cte_insert spec + proof: 2-3 days
- AutoCorres2 comparison document: 1 day
- **Total: 4-5 days**

## AutoCorres2 Comparison Points

1. **Proof size**: LOC of Clift proof vs AutoCorres2 proof
2. **Proof time**: Time to develop proof (human hours)
3. **Automation level**: How much is automated vs manual
4. **Axiom footprint**: What axioms each proof depends on
5. **Spec expressiveness**: Can both express the same properties?

## Risks

- cte_insert may require features Clift doesn't support yet
- AutoCorres2 proofs may use Isabelle features without Lean equivalents
- Bitfield extraction requires precise UInt64 reasoning
- seL4's actual cap operations are more complex than our simplified versions

## Prerequisites

- Task 0189: Reduce sorry count (provides proof pattern experience)
- Task 0207: Zero-sorry milestone (validates proof infrastructure)
- Conditional pattern proof helper (needed for isArchObjectType)
