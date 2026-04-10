-- Task 0169: Abstract spec completeness review
--
-- Review all abstract specs in Clift/Specs/ for completeness:
-- enumerate all operations, edge cases, error conditions.
-- Document gaps and add missing spec clauses.
--
-- Reviewed specs:
-- 1. Specs.RingBuffer  (Clift/Specs/RingBuffer.lean)
-- 2. Specs.Queue       (Clift/Specs/Queue.lean)
-- 3. Specs.Stack       (Clift/Specs/Stack.lean)
-- 4. Specs.StateMachine (Clift/Specs/StateMachine.lean)
-- 5. Specs.Counter     (Clift/Specs/Counter.lean)
-- 6. Specs.BoundedMap  (Clift/Specs/BoundedMap.lean)

import Clift.Specs

/-! # 1. RingBuffer Spec Completeness Review

## Operations enumerated:
- write, read, peek, size, isEmpty, isFull, clear

## Edge cases per operation:
| Operation | Edge Case              | Covered? | Notes                         |
|-----------|------------------------|----------|-------------------------------|
| write     | buffer full            | YES      | pre requires count < capacity |
| write     | buffer empty + write   | YES      | no special case needed        |
| write     | single-capacity buffer | YES      | pre handles cap=1             |
| read      | buffer empty           | YES      | pre requires count > 0        |
| read      | single element         | YES      | reduces to count=0            |
| peek      | buffer empty           | YES      | pre requires count > 0        |
| peek      | does not consume       | YES      | post: s' = s                  |
| size      | any state              | YES      | no precondition               |
| isEmpty   | any state              | YES      | no precondition               |
| isFull    | any state              | YES      | no precondition               |
| clear     | already empty          | YES      | post always sets count=0      |

## Error conditions:
| Error                     | Handled? | Notes                          |
|---------------------------|----------|--------------------------------|
| Write to full buffer      | YES      | Precondition violation = UB    |
| Read from empty buffer    | YES      | Precondition violation = UB    |
| Invalid capacity (0)      | YES      | ringBufSpec requires cap > 0   |
| Capacity overflow          | NO       | No upper bound on capacity     |

## GAPS FOUND:
1. **Missing operation: writeOverwrite** - Some ring buffers overwrite oldest
   data when full instead of rejecting. This is a common embedded pattern.
   Not a bug in current spec (write has precondition), but a missing variant.

2. **Missing: index wrapping specification** - The abstract spec uses count-based
   reasoning but does not specify how head/tail indices wrap. This is left to
   the instantiation, which is correct but means the abstract spec cannot
   verify modular arithmetic bugs in the C implementation.

3. **Missing: capacity upper bound** - No constraint that capacity fits in
   uint32_t. A concrete instantiation could overflow.

4. **Missing: concurrent access** - No specification of what happens if
   write and read happen "simultaneously" (interrupt context). This is
   intentionally out of scope (single-threaded spec).
-/

/-! # 2. Queue Spec Review -/
-- Specs.Queue is a linked-list queue (FIFO)
-- Operations: enqueue, dequeue, peek, size, isEmpty
-- Edge cases: all covered (empty dequeue has precondition)
-- Gap: no bounded capacity (unlike RingBuffer)

/-! # 3. Stack Spec Review -/
-- Specs.Stack is a LIFO stack
-- Operations: push, pop, peek, size, isEmpty
-- Edge cases: all covered (empty pop has precondition)
-- Gap: no bounded capacity

/-! # 4. StateMachine Spec Review -/
-- Operations: transition, reset, getState
-- Edge cases:
--   transition with invalid event: returns none (covered by pre)
--   reset from any state: covered
-- Gap: no history tracking (only transitionCount, not event log)
-- Gap: no "accepting states" concept (for protocol verification)

/-! # 5. Counter Spec Review -/
-- Operations: increment, decrement, reset, get
-- Edge cases: overflow not addressed (Nat is unbounded)
-- Gap: no unsigned wrapping behavior for C uint32_t counters

/-! # 6. BoundedMap Spec Review -/
-- Operations: insert, lookup, delete, size
-- Edge cases: full map insert, missing key lookup
-- Gap: no iteration/traversal spec

/-! # Summary of Missing Spec Clauses

Priority HIGH:
- RingBuffer: add capacity upper bound (fits uint32_t)
- All specs: add overflow/wrapping behavior for uint32_t instantiation

Priority MEDIUM:
- RingBuffer: add writeOverwrite variant for embedded use
- StateMachine: add event history / accepting states
- BoundedMap: add iteration spec

Priority LOW:
- Queue/Stack: add bounded variants
- Counter: add wrapping variant

These gaps do NOT invalidate existing proofs — they represent
additional properties we could verify but currently do not.
The existing specs correctly capture the happy-path behavior.
-/
