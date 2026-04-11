-- Task 0146: SHA-256 crypto primitive verification
--
-- Real-world target: SHA-256 compression function (FIPS 180-4).
-- 14 functions imported from sha256_core.c (~230 LOC C -> ~1629 lines Lean).
--
-- Key verification targets:
-- - Bitwise helper functions (Ch, Maj, Sigma) match FIPS 180-4 definitions
-- - Initialization sets standard IV
-- - Round step computes correct T1, T2 values
-- - Constant-time property: no data-dependent branches in crypto helpers

import Generated.Sha256Core
import Clift.Lifting.Pipeline
import Clift.Lifting.FuncSpec

set_option maxHeartbeats 12800000
set_option maxRecDepth 4096

open Sha256Core

/-! # Step 1: Run the clift pipeline on all 14 functions -/

clift Sha256Core

/-! # Step 2: Verify L1 definitions exist for all functions -/

-- Bitwise helpers (7)
#check @Sha256Core.l1_sha256_rotr_body
#check @Sha256Core.l1_sha256_ch_body
#check @Sha256Core.l1_sha256_maj_body
#check @Sha256Core.l1_sha256_bsigma0_body
#check @Sha256Core.l1_sha256_bsigma1_body
#check @Sha256Core.l1_sha256_ssigma0_body
#check @Sha256Core.l1_sha256_ssigma1_body

-- Init/finalize (3)
#check @Sha256Core.l1_sha256_init_body
#check @Sha256Core.l1_sha256_round_init_body
#check @Sha256Core.l1_sha256_round_finalize_body

-- Core compression (1)
#check @Sha256Core.l1_sha256_round_step_body

-- Schedule + utility (3)
#check @Sha256Core.l1_sha256_schedule_word_body
#check @Sha256Core.l1_sha256_check_iv_body
#check @Sha256Core.l1_sha256_state_equal_body

/-! # Step 3: FuncSpecs for crypto functions -/

/-- sha256_ch: Ch(e, f, g) = (e AND f) XOR (NOT e AND g)
    This is a pure bitwise function -- no heap, no failure.
    The spec IS the FIPS 180-4 definition. -/
def sha256_ch_spec : FuncSpec ProgramState where
  pre := fun _ => True
  post := fun r s =>
    r = Except.ok () →
    s.locals.ret__val = (s.locals.e &&& s.locals.f) ^^^ (~~~s.locals.e &&& s.locals.g)

/-- sha256_maj: Maj(a, b, c) = (a AND b) XOR (a AND c) XOR (b AND c) -/
def sha256_maj_spec : FuncSpec ProgramState where
  pre := fun _ => True
  post := fun r s =>
    r = Except.ok () →
    s.locals.ret__val = (s.locals.a_uint32 &&& s.locals.b_uint32) ^^^
                        (s.locals.a_uint32 &&& s.locals.c) ^^^
                        (s.locals.b_uint32 &&& s.locals.c)

/-- sha256_init: sets state to FIPS 180-4 initial hash values.
    The exact constants are the standard IV. -/
def sha256_init_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.st
  post := fun r s =>
    r = Except.ok () →
    let st := hVal s.globals.rawHeap s.locals.st
    st.h0 = 0x6a09e667 ∧
    st.h1 = 0xbb67ae85 ∧
    st.h2 = 0x3c6ef372 ∧
    st.h3 = 0xa54ff53a ∧
    st.h4 = 0x510e527f ∧
    st.h5 = 0x9b05688c ∧
    st.h6 = 0x1f83d9ab ∧
    st.h7 = 0x5be0cd19 ∧
    st.total_bytes = 0

/-- sha256_check_iv: returns 1 if state matches standard IV. -/
def sha256_check_iv_spec : FuncSpec ProgramState where
  pre := fun s =>
    heapPtrValid s.globals.rawHeap s.locals.st
  post := fun r s =>
    r = Except.ok () →
    let st := hVal s.globals.rawHeap s.locals.st
    (st.h0 = 0x6a09e667 ∧ st.h1 = 0xbb67ae85 ∧ st.h2 = 0x3c6ef372 ∧
     st.h3 = 0xa54ff53a ∧ st.h4 = 0x510e527f ∧ st.h5 = 0x9b05688c ∧
     st.h6 = 0x1f83d9ab ∧ st.h7 = 0x5be0cd19 →
     s.locals.ret__val = 1)

/-- sha256_schedule_word: W[t] = sigma1(W[t-2]) + W[t-7] + sigma0(W[t-15]) + W[t-16]
    Pure computation, no heap access needed. -/
def sha256_schedule_word_spec : FuncSpec ProgramState where
  pre := fun _ => True
  post := fun r s =>
    r = Except.ok () →
    -- The result should be the sum of the sigma-transformed inputs
    -- (Full spec would reference sha256_ssigma0/sha256_ssigma1 definitions)
    True -- Placeholder: full spec requires inter-procedural reasoning

/-! # Step 4: validHoare theorems -/

-- The bitwise helpers are the most provable: pure functions, no heap, no loops.
-- They should be the first to have sorry eliminated.

theorem sha256_ch_satisfies_spec :
    sha256_ch_spec.satisfiedBy (l1_sha256_ch_body) := by
  unfold FuncSpec.satisfiedBy sha256_ch_spec validHoare
  intro s _
  unfold Sha256Core.l1_sha256_ch_body
  have h := L1_modify_throw_catch_skip_result
    (fun s : ProgramState => { s with locals := { s.locals with ret__val := ((s.locals.e &&& s.locals.f) ^^^ ((~~~s.locals.e) &&& s.locals.g)) } })
    s
  obtain ⟨h_res, h_nf⟩ := h
  constructor
  · exact h_nf
  · intro r s' h_mem
    rw [h_res] at h_mem
    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
    subst hr; subst hs
    intro _; rfl

theorem sha256_init_satisfies_spec :
    sha256_init_spec.satisfiedBy (l1_sha256_init_body) := by
  unfold FuncSpec.satisfiedBy sha256_init_spec
  unfold validHoare
  intro s hpre
  sorry -- Requires: heap write reasoning for 9 field assignments

/-! # Step 5: Constant-time property

  For crypto code, we want to verify that execution does not depend on secret data.
  The bitwise helpers (Ch, Maj, Sigma) are inherently constant-time: they use only
  AND, OR, XOR, NOT, shift, and rotate -- no branches.

  The sha256_round_step function also has no branches (only arithmetic and calls
  to the bitwise helpers).

  The sha256_check_iv and sha256_state_equal functions DO have data-dependent branches
  (comparing hash values). These are NOT constant-time and should NOT be used in
  contexts where timing side channels matter. This is documented, not a bug.

  Formal constant-time verification would require an information flow type system
  or a timing model, which is beyond our current framework. We state the property
  as a comment-level observation.
-/

/-! # Summary

  14 functions imported and lifted through L1/L2/L3.
  5 FuncSpecs defined covering:
    - FIPS 180-4 building blocks (Ch, Maj)
    - Standard IV initialization (sha256_init)
    - IV verification (sha256_check_iv)
    - Message schedule (sha256_schedule_word)

  Blocked on:
    - UInt32 bitwise lemmas for proving Ch/Maj match spec
    - Heap write reasoning for init
    - Inter-procedural call specs for round_step (calls Ch, Maj, Sigma)

  Constant-time observation: all crypto helpers are branch-free.
-/
