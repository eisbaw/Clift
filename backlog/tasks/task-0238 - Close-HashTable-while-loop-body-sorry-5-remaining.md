---
id: TASK-0238
title: Close HashTable while loop body sorry (5 remaining)
status: To Do
assignee: []
created_date: '2026-04-13 09:53'
labels:
  - sorry-elimination
  - hash-table
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
5 sorry in HashTableProof.lean, all in while loop body obligations after dynCom is proven.

LOOKUP (2 sorry):
- h_body_inv (line 919): prove invariant preserved on continue path (advance idx/probes). Needs anonymous constructor step functions for idx=(idx+1)&cap_mask and probes++. Use idx_advance_bounded for idx < capacity.
- h_abrupt (line 926): prove throw paths set ret_val ∈ {0,1}. Use lk_set_ret0/ret1 funext lemmas + L1_modify_throw_only_error'.

INSERT (3 sorry):
- h_body_nf (line 1063): same pattern as proven lookup h_body_nf but with heapUpdate in insert branch. Use heapUpdate_preserves_heapPtrValid for guards after heap writes.
- h_body_inv (line 1066): same as lookup h_body_inv.
- h_abrupt (line 1071): same as lookup h_abrupt but ret_val=0 on both paths.

KEY TECHNIQUE: Every { s with locals := ... } in the loop body MUST use anonymous constructors for the 13-field Locals (cap_mask, capacity, h, ht, i, idx, key, keys, out, probes, ret__val, value, values). Any subst/rw that expands a struct update triggers kernel deep recursion.

TEMPLATE: lookup h_body_nf (just proven, line 879-924) shows the NondetM decomposition pattern using L1_seq_failed_iff + L1_guard_not_failed.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 ht_lookup h_body_inv proven
- [ ] #2 ht_lookup h_abrupt proven
- [ ] #3 ht_insert h_body_nf proven
- [ ] #4 ht_insert h_body_inv proven
- [ ] #5 ht_insert h_abrupt proven
<!-- AC:END -->
