# ADR-007: No Address-of Locals (StrictC Restriction)

## Status
Accepted

## Context
Real embedded C frequently uses `&local_var` to pass local variables by reference (out-parameters, passing local arrays to functions). Supporting this in the formal model requires fundamentally changing how locals are represented: instead of simple record fields, addressed locals must be heap-allocated or modeled via a stack frame.

## Decision
**Reject address-of-locals with a clear error.** The CImporter raises `StrictCViolation` when it encounters the `&` (address-of) unary operator applied to a local variable.

This matches seL4's StrictC restriction. The seL4 C parser (AutoCorres2) also forbids taking the address of local variables.

## Rationale

1. **Memory model simplicity**: Locals as record fields enables clean L2 LocalVarExtract (lifting locals to lambda-bound Lean variables). Heap-allocating addressed locals would break this clean abstraction.

2. **seL4 precedent**: The seL4 microkernel, the gold standard for verified C, enforces this restriction. If it is sufficient for a production microkernel, it is sufficient for our use cases.

3. **Implementation cost**: Supporting addressed locals would require either:
   - (a) Heap-allocating addressed locals and treating them as pointers (moderate: changes CImporter + L2 lifting)
   - (b) A full stack frame model with allocation on entry and deallocation on return (hard: new memory region type, stack validity proofs)
   Both options add significant complexity to the pipeline and all downstream proofs.

4. **Workaround**: C code that uses `&local` can usually be refactored to pass the value and return a modified value, or to use a heap-allocated struct.

## Future Path
If address-of-locals becomes necessary (e.g., for verifying code that cannot be refactored):

- **Option 1**: Heap-allocate addressed locals. Locals that have `&` taken get allocated in the heap model on function entry. Their "local" field in the Locals record is actually a `Ptr`. Function return deallocates them. This is moderate complexity.

- **Option 2**: Stack frame model (like AutoCorres2's Stack_Typing.thy). Define a stack region in the heap, allocate locals there on function entry, deallocate on exit. This gives the most accurate C semantics but is the hardest to implement.

Recommendation for future: Option 1, as it's simpler and composes with the existing heap model.

## Consequences
- C code using `&local_var` will be rejected with a clear error message
- Users must refactor such code before verification
- The memory model and L2 lifting remain clean and simple
- All proofs avoid reasoning about stack frame validity
