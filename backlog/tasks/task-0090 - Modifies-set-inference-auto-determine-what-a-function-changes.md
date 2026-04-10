---
id: TASK-0090
title: 'Modifies-set inference: auto-determine what a function changes'
status: To Do
assignee: []
created_date: '2026-04-10 05:18'
labels:
  - phase-c
  - automation
  - seplogic
dependencies:
  - TASK-0089
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
For each function, automatically infer which heap locations and state fields it modifies. This is essential for the frame rule: if f modifies only {a, b}, then any assertion about locations outside {a, b} is preserved. Study AutoCorres2's approach — it tracks modifies sets through the lifting stages. The modifies set can be computed statically from the CSimpl body (which locations appear in heapUpdate calls).
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 modifiesSet function: CSimpl -> Set of modified locations
- [ ] #2 Static analysis: extract heapUpdate targets from CSimpl body
- [ ] #3 Modifies set preserved through L1 lifting
- [ ] #4 Frame theorem: if loc not in modifiesSet, assertion about loc preserved
- [ ] #5 Tested on swap (modifies {*a, *b}), gcd (modifies nothing in heap)
<!-- AC:END -->
