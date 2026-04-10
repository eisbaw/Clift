---
id: TASK-0108
title: 'Full L2 LocalVarExtract: rewrite computation, not wrapper'
status: To Do
assignee: []
created_date: '2026-04-10 12:58'
labels:
  - scalability
  - lifting
dependencies: []
references:
  - ext/AutoCorres2/local_var_extract.ML
  - ext/AutoCorres2/LocalVarExtract.thy
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Current L2 is a wrapper (l2_wrap) that takes locals as arguments. seL4's L2 genuinely rewrites the monadic computation to eliminate the locals record from the state type — every L1.modify that touches locals becomes a pure let-binding. This matters at scale: wrapper-based L2 still carries the full CState type in proofs, making them verbose. The real L2 produces cleaner types that are faster to check.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 L2 rewrites L1 computation (not just wraps it)
- [ ] #2 State type after L2 is Globals only (no Locals record)
- [ ] #3 Local variable reads become references to lambda-bound vars
- [ ] #4 Local variable writes become state threading via let
- [ ] #5 L2corres proven (backward simulation)
- [ ] #6 clift_l2 MetaM updated to use rewrite approach
<!-- AC:END -->
