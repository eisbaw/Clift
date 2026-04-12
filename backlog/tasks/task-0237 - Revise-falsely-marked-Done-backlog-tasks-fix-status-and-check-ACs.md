---
id: TASK-0237
title: 'Revise falsely-marked-Done backlog tasks: fix status and check ACs'
status: To Do
assignee: []
created_date: '2026-04-12 21:47'
updated_date: '2026-04-12 21:48'
labels:
  - housekeeping
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Bulk status update around 2026-04-10 incorrectly marked ~120 tasks as Done without checking individual AC completion. An audit using 20 parallel agents reviewed each task against git history and codebase evidence. Tasks fall into three categories that need different remediation.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 Fix 27 ACTUALLY DONE tasks: leave as Done but check their unchecked ACs to match reality
- [ ] #2 Fix 29 NOT DONE tasks: reset status to To Do
- [ ] #3 Fix ~65 PARTIALLY DONE tasks: reset status to In Progress or To Do (decide policy)
- [ ] #4 Verify all changes are consistent after bulk update
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
## Audit Results (2026-04-12)

Root cause: bulk status update around 2026-04-10 marked all roadmap tasks as Done without checking AC completion.

---

### ACTUALLY DONE (27 tasks) — leave as Done, check their ACs

These have real completed work in git but AC checkboxes were never ticked.

- TASK-0048: corres_auto tactic — AC#4 measurement answered in final summary
- TASK-0049: Test on real embedded C — pipeline limitation is documented blocker
- TASK-0056: Add spec/dynCom/call combinators — deferred items by design decision
- TASK-0062: l1_swap_validHoare proof — commit 99966ec, 0 sorry
- TASK-0068: MemType surjection — documentation exists in State.lean:392
- TASK-0121: CImporter address-of locals — approach changed to reject-and-document per StrictC
- TASK-0142: Exec semantics audit — ExecAudit.lean 11KB, 0 sorry, 22 rules
- TASK-0167: Inline assembly boundary — AsmBoundary.lean 226 LOC, 0 sorry
- TASK-0170: Termination predicate — TerminatesProps.lean + TerminationProofs.lean, 7 functions
- TASK-0171: Optimized-vs-clean equivalence — OptEquiv.lean 244 LOC, 0 sorry
- TASK-0176: Capability system verification — Capabilities.lean 149 LOC, 0 sorry
- TASK-0182: Sorry audit — zero sorry in core, SorryAudit.lean exists, CI metric in verify.yml
- TASK-0184: TCB documentation — docs/tcb.md covers all 5 ACs
- TASK-0188: BSD LICENSE and ATTRIBUTION.md — both exist at repo root
- TASK-0191: Eliminate 7 sorry Sel4CapProof — commit 5cd2077, 0 sorry
- TASK-0194: Eliminate 5 sorry DmaBufferProof — commits cff835a/cecd3c1, 0 sorry
- TASK-0195: Eliminate 4 sorry RbtreeProof — commits d37248f/c650ca8, 0 sorry
- TASK-0196: Eliminate 4 sorry MemAllocProof — model-race eliminated last sorry
- TASK-0197: Eliminate 3 sorry RtosQueueProof — race 5 eliminated queue_create/peek
- TASK-0198: Eliminate 3 sorry StateMachineProof — commits d37248f/c650ca8, 0 sorry
- TASK-0199: Eliminate 2 sorry Sha256CoreProof — race 6 proved sha256_init
- TASK-0200: Eliminate 2 sorry PacketParserProof — commit a837868, 0 sorry
- TASK-0201: Eliminate 2 sorry UartDriverProof — commit 5be244b, 0 sorry
- TASK-0202: Eliminate 2 sorry ArrayBoundsProof — commit 7de6eed, 0 sorry
- TASK-0203: Eliminate 1 sorry SystemCorrectness — commit 7de6eed, 0 sorry
- TASK-0229: Extend L1_hoare_guard_modify_chain to N steps — commit c29481b, 0 sorry

Note: TASK-0153 (paper) was already fixed to To Do during this audit.

---

### NOT DONE (29 tasks) — reset to To Do

No real implementation work, or only design docs/planning documents exist.

- TASK-0073: Function pointers/dispatch tables — final summary says "Deferred to Phase 5+"
- TASK-0075: Scale testing 500-1000 LOC — only 224 LOC across small files
- TASK-0078: Incremental re-verification — no code, just analysis doc
- TASK-0089: Phase B milestone 10-function file — only 5 functions, 2 auto-proved
- TASK-0094: Phase C milestone <5:1 proof ratio — actual ratio 16:1 to 77:1
- TASK-0098: Verify 1000+ LOC module — only 4 specs written (needs 20)
- TASK-0103: Phase E milestone AI-assisted — framework only, no measurements
- TASK-0139: Prove absence of all UB in ring_buffer_ext — all sorry, file deleted
- TASK-0148: Verify protocol parser MQTT/CoAP — no code at all
- TASK-0149: Proof maintenance test — no experiments or reports
- TASK-0150: Lean 4 version upgrade test — toolchain unchanged
- TASK-0151: Performance hardening 100+ functions — no benchmarks
- TASK-0152: Publish on Lean 4 Reservoir — not published
- TASK-0154: External review by formal methods expert — no reviewer evidence
- TASK-0155: Contribute CImporter upstream — no upstream diff
- TASK-0173: WCET/timing analysis — design doc only, no Lean code
- TASK-0185: Availability proof DoS prevention — skeleton model only, 0 theorems
- TASK-0186: Pointer arithmetic and array bounds — zero implementation
- TASK-0187: Backlog dependency map — no systematic review done
- TASK-0205: Batch sorry elimination — superseded, never executed
- TASK-0206: Manual proof for sorry — superseded along with TASK-0205
- TASK-0208: Proof engine context window management — design doc only
- TASK-0209: Proof engine learn from failures — design doc only
- TASK-0212: Second verification campaign — planning doc only
- TASK-0213: Third verification campaign seL4 caps — 3/6 functions, 2 sorry remain
- TASK-0214: Mutation testing — script exists but never actually run, no results
- TASK-0217: Proof repair automation — design doc only
- TASK-0218: Benchmark against AutoCorres2 — doc exists but benchmark never run

---

### PARTIALLY DONE (~65 tasks) — reset to In Progress or To Do

Real code artifacts exist but 1-5 ACs represent genuinely missing functionality.

**Pipeline phases (deferred MetaM automation or test cases):**
- TASK-0019: CImporter emit CSimpl (6/7 AC) — AC#5 signed overflow deferred to TASK-0072
- TASK-0023: SimplConv L1 MetaM (4/6 AC) — AC#4-5 cond/while deferred to TASK-0061
- TASK-0024: LocalVarExtract L2 (0/5 AC) — foundation stub only, no MetaM transform
- TASK-0025: Phase 1 end-to-end (3/6 AC) — L2corres, validHoare, corres_trans unfinished
- TASK-0028: TypeStrengthen L3 MetaM (3/5 AC) — only pure path, no option/nondet typing
- TASK-0029: WordAbstract L5 define (3/4 AC) — signed word abstraction deferred
- TASK-0030: WordAbstract L5 MetaM (3/4 AC) — only 1 manual proof, no automation
- TASK-0031: CStep tactic (2/4 AC) — no totalHoare, no gcd test
- TASK-0032: Phase 2 end-to-end (4/5 AC) — chain uses bridge not composed corres
- TASK-0036: Phase 3a swap.c (2/4 AC) — swap_correct depends on sorry
- TASK-0042: HeapLift L4 MetaM (1/4 AC) — MetaM automation deferred to Phase 4
- TASK-0044: Phase 3 list_length.c (3/5 AC) — list_length not attempted
- TASK-0046: CVcg tactic (2/5 AC) — no spec lookup, no loop invariants

**CImporter features (edge cases deferred):**
- TASK-0088: Multi-function C files (5/6 AC) — pointer args to calls not addressed
- TASK-0106: Array subscript (4/6 AC) — local array decls and struct array fields deferred
- TASK-0107: L1corres mutual recursion (2/6 AC) — only topo sort done, no fixed-point
- TASK-0108: Full L2 LocalVarExtract (5/6 AC) — MetaM still uses wrapper approach

**Verification examples (imported but incomplete proofs):**
- TASK-0140: CImporter fuzz testing (0/5 AC) — script exists, never run at scale
- TASK-0141: Integer promotion audit (0/6 AC) — test infra exists, no CImporter fixes
- TASK-0143: Memory model audit (0/6 AC) — stub tests only
- TASK-0145: Verify FreeRTOS queue.c (0/6 AC) — 3/10+ functions proven
- TASK-0146: Verify crypto SHA-256 (0/6 AC) — 2 theorems proven, compression not done
- TASK-0147: Verify UART driver (0/6 AC) — only uart_init proven
- TASK-0156: Verify seL4 C code (0/6 AC) — 7 functions imported, 5 theorems proven
- TASK-0157: Hash table (0/6 AC) — 3 sorry remain
- TASK-0158: Memory allocator (0/6 AC) — init+accessors only, not malloc/free
- TASK-0159: Red-black tree (0/6 AC) — BST property proven, no color/balance invariants
- TASK-0160: State machine (0/5 AC) — partial, no deadlock-freedom proof
- TASK-0161: Priority queue (0/5 AC) — C source only 127 LOC (needs 250+), 4 sorry
- TASK-0162: DMA buffer (0/5 AC) — 0 sorry but C source only 110 LOC (needs 200+)
- TASK-0163: Packet parser (0/5 AC) — proof file only 260 lines with #check stubs

**seL4 patterns (abstract models only, no C verification):**
- TASK-0074: Interrupt handler verification (0/3 AC) — models only
- TASK-0164: Concurrency/preemption model (0/6 AC) — 4/6 ACs at abstract level
- TASK-0165: Multi-architecture (0/6 AC) — types defined, no CImporter --arch flag
- TASK-0168: Compiler extensions (0/6 AC) — types defined, no CImporter integration
- TASK-0172: System init verification (0/4 AC) — framework exists, no ring_buffer_init
- TASK-0177: Page table verification (0/4 AC) — abstract model, no C verified
- TASK-0178: Scheduler verification (0/4 AC) — abstract model, no C verified
- TASK-0179: Interrupt handling (0/4 AC) — abstract model, no C verified
- TASK-0180: Exception/fault delivery (0/4 AC) — abstract model, no C verified
- TASK-0181: Authority confinement (0/4 AC) — abstract model, no composition proof
- TASK-0183: C11 coverage doc (0/5 AC) — doc exists but Annex J UB incomplete

**Proof infrastructure (frameworks built, targets not hit):**
- TASK-0071: CVcg MetaM flat proof terms (0/4 AC) — swap fixed differently, no MetaM VCG
- TASK-0076: Lean 4 kernel depth issue (0/3 AC) — workaround done, no upstream report
- TASK-0087: MetaM VCG decompose (2/7 AC) — call_spec rules exist, no tests
- TASK-0091: Weakest precondition calculus (3/6 AC) — wp_sound done, no completeness
- TASK-0093: Linked list traversal (4/6 AC) — isList done, validHoare deferred
- TASK-0096: Global invariant framework (4/5 AC) — no VCG integration
- TASK-0104: Evaluate Mathlib (0/5 AC) — decision made but no measurements
- TASK-0105: MetaM VCG flat proof terms (0/6 AC) — basic l1_vcg exists, not scalable
- TASK-0113: seL4-scale attempt (5/8 AC) — 676 LOC imported, no actual verification
- TASK-0114: Re-evaluate Mathlib (3/5 AC) — AC#1 prerequisite not met
- TASK-0115: clift-prove-by-claudecode (11/14 AC) — mock only, no real API
- TASK-0116: Full Hoare triples ring_buffer_ext (4/6 AC) — 5/40 sorry-free
- TASK-0118: Abstract spec refinement (4/6 AC) — 16 sorry in refinement file
- TASK-0138: System-level correctness (0/5 AC) — sorry chain not eliminated

**AI/automation (frameworks, no measurements):**
- TASK-0099: AI loop invariant generation (4/6 AC) — no retry logic, no success rate
- TASK-0100: AI data structure invariant (3/5 AC) — no queue test, no measurement
- TASK-0102: RAG index over lemmas (3/4 AC) — no improvement measurement

**Other partially done:**
- TASK-0070: L2 LocalVarExtract full (3/4 AC) — rotate3 not tested
- TASK-0086: Function spec framework (5/6 AC) — no caller/callee test
- TASK-0128: Binary verification (3/4 AC) — ADR-008 missing from disk
- TASK-0137: Full functional correctness (4/6 AC) — frame conditions partial, proofs sorry
- TASK-0204: Wire proof engine to Claude API (5/6 AC) — never run with real API key
- TASK-0210: Generate irreducible+projection lemmas (3/5 AC) — not integrated
- TASK-0221: Prove rb_push validHoare (1/4 AC) — proven but via different technique
- TASK-0222: Loop body preservation (3/4 AC) — rb_sum has trivial postcondition
<!-- SECTION:NOTES:END -->
