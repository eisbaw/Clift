# Task Dependency Map

Generated 2026-04-08. Covers all To Do tasks with explicit blocking relationships.

## Legend

- `A -> B` means A blocks B (B cannot start until A is done)
- **Critical path** items are marked with `[CP]`

## Dependency Graph

### Sorry Elimination Chain

These tasks eliminate sorry from proof files. They are independent of each other
but collectively block external review (0154) and paper (0153).

```
0189 (RBExtFuncSpecs sorry)     --\
0190 (RBExtRefinement sorry)     |--> 0154 (external review)
0191 (Sel4CapProof sorry)        |
0192 (PriorityQueue sorry)       |
0193 (HashTable sorry)           |
0194 (DmaBuffer sorry)           |
0195 (Rbtree sorry)              |
0196 (MemAlloc sorry)            |
0197 (RtosQueue sorry)           |
0198 (StateMachine sorry)        |
0199 (Sha256Core sorry)          |
0200 (PacketParser sorry)        |
0201 (UartDriver sorry)          |
0202 (ArrayBounds sorry)         |
0203 (SystemCorrectness sorry)  --/
```

### Concurrency / Interrupt Chain

```
0167 (ASM boundary)     --> 0164 (concurrency model)  --> 0179 (interrupt handling)
0168 (compiler ext)     --> 0164 (volatile needed for shared state)
```

Rationale: The concurrency model (0164) needs ASM primitives for disable_irq/enable_irq
(0167) and volatile semantics (0168) for shared state. Interrupt handling verification
(0179) requires the concurrency model.

### System Correctness Chain [CP]

```
0172 (init verification)  --> 0138 (composed system correctness) [in progress]
0174 (invariant preservation) [done] --> 0172 (init must establish preserved invariants)
0171 (opt-vs-clean equiv) --> independent, but useful for 0156 (seL4 verification)
```

### seL4 Parity Chain [CP]

```
0164 (concurrency)       --\
0165 (multi-arch)         |
0167 (ASM boundary)       |--> 0156 (verify seL4 C code)
0168 (compiler ext)       |
0176 (capability system)  |
0177 (virtual memory)     |
0178 (scheduler)         --/
```

All of these are prerequisites for attempting seL4 C code verification.

### Capability / Security Chain

```
0176 (capability system)  --> 0181 (authority confinement)
0125 (security framework) [done] --> 0176 (capability system)
0125 (security framework) [done] --> 0185 (availability proof)
```

### OS Verification Chain

```
0177 (virtual memory)    --> 0156 (seL4 verification)
0178 (scheduler)         --> 0156 (seL4 verification)
0179 (interrupt handling) --> 0156 (seL4 verification)
0180 (exception/fault)   --> 0156 (seL4 verification)
```

### Infrastructure / Tooling

```
0165 (multi-arch)        --> 0152 (publish on Reservoir, needs arch flexibility)
0166 (regression suite) [done] --> 0152 (publish, needs CI)
0188 (LICENSE)           --> 0152 (publish, needs license)
```

### External-Facing

```
0154 (external review)   --> 0153 (paper, review feedback improves paper)
0152 (publish)           --> 0153 (paper, needs published artifact)
```

## Blocked Tasks (prerequisites not met)

| Task | Blocked By | Status of Blocker |
|------|-----------|-------------------|
| 0156 (seL4 verification) | 0164, 0165, 0167, 0168, 0176, 0177, 0178 | All To Do |
| 0179 (interrupt handling) | 0164 (concurrency) | To Do |
| 0181 (authority confinement) | 0176 (capability system) | To Do |
| 0154 (external review) | sorry tasks 0189-0203 | All To Do |

## Independent Tasks (no blockers, can start now)

- 0152 (publish on Reservoir) - only soft-blocked by 0188 (license)
- 0165 (multi-arch parameterization)
- 0167 (ASM boundary)
- 0168 (compiler extensions)
- 0171 (opt-vs-clean equivalence)
- 0172 (init verification)
- 0173 (WCET/timing analysis)
- 0185 (availability proof)
- 0188 (LICENSE file)
- 0189-0203 (sorry elimination tasks)

## Critical Path

The longest dependency chain to the ultimate goal (seL4 C code verification, 0156):

```
[CP] 0167 (ASM) --> 0164 (concurrency) --> 0179 (interrupts) --> 0156 (seL4)
```

Estimated: 4 tasks deep. Each is a multi-week effort.

Secondary critical path (capability system):

```
[CP] 0176 (capabilities) --> 0181 (confinement) --> 0156 (seL4)
```

## In-Progress Tasks

- 0136 (RBExtFuncSpecs validHoare proofs) - HIGH priority, blocks 0190
- 0175 (end-to-end refinement chain) - HIGH priority, foundational

## Recommendations

1. **Start with 0167 (ASM boundary)** - it unblocks 0164 (concurrency)
   which is on the critical path.

2. **Sorry elimination (0189-0203)** can proceed in parallel with
   framework tasks. They are independent of each other.

3. **0172 (init verification)** is independent and high-value: it closes
   the gap between "assume invariants" and "prove invariants established."

4. **0165 (multi-arch)** and **0168 (compiler ext)** are independent and
   can proceed in parallel.
