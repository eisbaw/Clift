---
id: TASK-0160
title: 'Example: verify a state machine (TCP-like connection states)'
status: To Do
assignee: []
created_date: '2026-04-10 18:47'
labels:
  - phase-n
  - examples
  - state-machine
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
State machines are core to protocol implementations, device drivers, and embedded systems. Write a ~200 LOC state machine: 5-10 states, transitions with guards, event handlers. Model after TCP connection states (CLOSED, LISTEN, SYN_SENT, ESTABLISHED, etc.). Prove: only valid transitions occur, invariant preserved in every state, no deadlock from valid initial state.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 State machine C source (200+ LOC)
- [ ] #2 State transition spec defined (graph of valid transitions)
- [ ] #3 Only valid transitions proven
- [ ] #4 State invariant preserved in all states
- [ ] #5 No deadlock from initial state
<!-- AC:END -->
