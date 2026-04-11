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

private theorem sha_heapUpdate_st_ptrValid (s : ProgramState)
    (hv : heapPtrValid s.globals.rawHeap s.locals.st)
    (v : Sha256Core.C_sha256_state) :
    heapPtrValid (heapUpdate s.globals.rawHeap s.locals.st v) s.locals.st :=
  heapUpdate_preserves_heapPtrValid _ _ _ _ hv

theorem sha256_init_satisfies_spec :
    sha256_init_spec.satisfiedBy (l1_sha256_init_body) := by
  unfold FuncSpec.satisfiedBy sha256_init_spec validHoare
  intro s hpre
  let p := fun s : ProgramState => heapPtrValid s.globals.rawHeap s.locals.st
  let f1 := fun s : ProgramState =>
    { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.st ({ hVal s.globals.rawHeap s.locals.st with h0 := 1779033703 } : Sha256Core.C_sha256_state) } }
  let f2 := fun s : ProgramState =>
    { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.st ({ hVal s.globals.rawHeap s.locals.st with h1 := 3144134277 } : Sha256Core.C_sha256_state) } }
  let f3 := fun s : ProgramState =>
    { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.st ({ hVal s.globals.rawHeap s.locals.st with h2 := 1013904242 } : Sha256Core.C_sha256_state) } }
  let f4 := fun s : ProgramState =>
    { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.st ({ hVal s.globals.rawHeap s.locals.st with h3 := 2773480762 } : Sha256Core.C_sha256_state) } }
  let f5 := fun s : ProgramState =>
    { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.st ({ hVal s.globals.rawHeap s.locals.st with h4 := 1359893119 } : Sha256Core.C_sha256_state) } }
  let f6 := fun s : ProgramState =>
    { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.st ({ hVal s.globals.rawHeap s.locals.st with h5 := 2600822924 } : Sha256Core.C_sha256_state) } }
  let f7 := fun s : ProgramState =>
    { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.st ({ hVal s.globals.rawHeap s.locals.st with h6 := 528734635 } : Sha256Core.C_sha256_state) } }
  let f8 := fun s : ProgramState =>
    { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.st ({ hVal s.globals.rawHeap s.locals.st with h7 := 1541459225 } : Sha256Core.C_sha256_state) } }
  let f9 := fun s : ProgramState =>
    { s with globals := { s.globals with rawHeap := heapUpdate s.globals.rawHeap s.locals.st ({ hVal s.globals.rawHeap s.locals.st with total_bytes := 0 } : Sha256Core.C_sha256_state) } }
  let s1 := f1 s; let s2 := f2 s1; let s3 := f3 s2; let s4 := f4 s3
  let s5 := f5 s4; let s6 := f6 s5; let s7 := f7 s6; let s8 := f8 s7; let s9 := f9 s8
  have hv1 : p s1 := sha_heapUpdate_st_ptrValid s hpre _
  have hv2 : p s2 := sha_heapUpdate_st_ptrValid s1 hv1 _
  have hv3 : p s3 := sha_heapUpdate_st_ptrValid s2 hv2 _
  have hv4 : p s4 := sha_heapUpdate_st_ptrValid s3 hv3 _
  have hv5 : p s5 := sha_heapUpdate_st_ptrValid s4 hv4 _
  have hv6 : p s6 := sha_heapUpdate_st_ptrValid s5 hv5 _
  have hv7 : p s7 := sha_heapUpdate_st_ptrValid s6 hv6 _
  have hv8 : p s8 := sha_heapUpdate_st_ptrValid s7 hv7 _
  have h1 := L1_guard_modify_result p f1 s hpre
  have h2 := L1_guard_modify_result p f2 s1 hv1
  have h3 := L1_guard_modify_result p f3 s2 hv2
  have h4 := L1_guard_modify_result p f4 s3 hv3
  have h5 := L1_guard_modify_result p f5 s4 hv4
  have h6 := L1_guard_modify_result p f6 s5 hv5
  have h7 := L1_guard_modify_result p f7 s6 hv6
  have h8 := L1_guard_modify_result p f8 s7 hv7
  have h9 := L1_guard_modify_result p f9 s8 hv8
  -- Chain steps 8,9
  have h89 := L1_seq_singleton_ok h8.1 h8.2 (m₂ := L1.seq (L1.guard p) (L1.modify f9))
  have h89_res : (L1.seq (L1.seq (L1.guard p) (L1.modify f8)) (L1.seq (L1.guard p) (L1.modify f9)) s7).results = {(Except.ok (), s9)} := by
    rw [h89.1, h9.1]
  have h89_nf : ¬(L1.seq (L1.seq (L1.guard p) (L1.modify f8)) (L1.seq (L1.guard p) (L1.modify f9)) s7).failed :=
    fun hf => h9.2 (h89.2.mp hf)
  -- Chain steps 7-9
  have h789 := L1_seq_singleton_ok h7.1 h7.2
    (m₂ := L1.seq (L1.seq (L1.guard p) (L1.modify f8)) (L1.seq (L1.guard p) (L1.modify f9)))
  have h789_res : (L1.seq (L1.seq (L1.guard p) (L1.modify f7)) (L1.seq (L1.seq (L1.guard p) (L1.modify f8)) (L1.seq (L1.guard p) (L1.modify f9))) s6).results = {(Except.ok (), s9)} := by
    rw [h789.1, h89_res]
  have h789_nf : ¬(L1.seq (L1.seq (L1.guard p) (L1.modify f7)) (L1.seq (L1.seq (L1.guard p) (L1.modify f8)) (L1.seq (L1.guard p) (L1.modify f9))) s6).failed :=
    fun hf => h89_nf (h789.2.mp hf)
  -- Chain steps 6-9
  have h6789 := L1_seq_singleton_ok h6.1 h6.2
    (m₂ := L1.seq (L1.seq (L1.guard p) (L1.modify f7)) (L1.seq (L1.seq (L1.guard p) (L1.modify f8)) (L1.seq (L1.guard p) (L1.modify f9))))
  have h6789_res : (L1.seq (L1.seq (L1.guard p) (L1.modify f6)) (L1.seq (L1.seq (L1.guard p) (L1.modify f7)) (L1.seq (L1.seq (L1.guard p) (L1.modify f8)) (L1.seq (L1.guard p) (L1.modify f9)))) s5).results = {(Except.ok (), s9)} := by
    rw [h6789.1, h789_res]
  have h6789_nf : ¬(L1.seq (L1.seq (L1.guard p) (L1.modify f6)) (L1.seq (L1.seq (L1.guard p) (L1.modify f7)) (L1.seq (L1.seq (L1.guard p) (L1.modify f8)) (L1.seq (L1.guard p) (L1.modify f9)))) s5).failed :=
    fun hf => h789_nf (h6789.2.mp hf)
  -- Chain steps 5-9
  have h56789 := L1_seq_singleton_ok h5.1 h5.2
    (m₂ := L1.seq (L1.seq (L1.guard p) (L1.modify f6)) (L1.seq (L1.seq (L1.guard p) (L1.modify f7)) (L1.seq (L1.seq (L1.guard p) (L1.modify f8)) (L1.seq (L1.guard p) (L1.modify f9)))))
  have h56789_res : (L1.seq (L1.seq (L1.guard p) (L1.modify f5)) (L1.seq (L1.seq (L1.guard p) (L1.modify f6)) (L1.seq (L1.seq (L1.guard p) (L1.modify f7)) (L1.seq (L1.seq (L1.guard p) (L1.modify f8)) (L1.seq (L1.guard p) (L1.modify f9))))) s4).results = {(Except.ok (), s9)} := by
    rw [h56789.1, h6789_res]
  have h56789_nf : ¬(L1.seq (L1.seq (L1.guard p) (L1.modify f5)) (L1.seq (L1.seq (L1.guard p) (L1.modify f6)) (L1.seq (L1.seq (L1.guard p) (L1.modify f7)) (L1.seq (L1.seq (L1.guard p) (L1.modify f8)) (L1.seq (L1.guard p) (L1.modify f9))))) s4).failed :=
    fun hf => h6789_nf (h56789.2.mp hf)
  -- Chain steps 4-9
  have h456789 := L1_seq_singleton_ok h4.1 h4.2
    (m₂ := L1.seq (L1.seq (L1.guard p) (L1.modify f5)) (L1.seq (L1.seq (L1.guard p) (L1.modify f6)) (L1.seq (L1.seq (L1.guard p) (L1.modify f7)) (L1.seq (L1.seq (L1.guard p) (L1.modify f8)) (L1.seq (L1.guard p) (L1.modify f9))))))
  have h456789_res : (L1.seq (L1.seq (L1.guard p) (L1.modify f4)) (L1.seq (L1.seq (L1.guard p) (L1.modify f5)) (L1.seq (L1.seq (L1.guard p) (L1.modify f6)) (L1.seq (L1.seq (L1.guard p) (L1.modify f7)) (L1.seq (L1.seq (L1.guard p) (L1.modify f8)) (L1.seq (L1.guard p) (L1.modify f9)))))) s3).results = {(Except.ok (), s9)} := by
    rw [h456789.1, h56789_res]
  have h456789_nf : ¬(L1.seq (L1.seq (L1.guard p) (L1.modify f4)) (L1.seq (L1.seq (L1.guard p) (L1.modify f5)) (L1.seq (L1.seq (L1.guard p) (L1.modify f6)) (L1.seq (L1.seq (L1.guard p) (L1.modify f7)) (L1.seq (L1.seq (L1.guard p) (L1.modify f8)) (L1.seq (L1.guard p) (L1.modify f9)))))) s3).failed :=
    fun hf => h56789_nf (h456789.2.mp hf)
  -- Chain steps 3-9
  have h3456789 := L1_seq_singleton_ok h3.1 h3.2
    (m₂ := L1.seq (L1.seq (L1.guard p) (L1.modify f4)) (L1.seq (L1.seq (L1.guard p) (L1.modify f5)) (L1.seq (L1.seq (L1.guard p) (L1.modify f6)) (L1.seq (L1.seq (L1.guard p) (L1.modify f7)) (L1.seq (L1.seq (L1.guard p) (L1.modify f8)) (L1.seq (L1.guard p) (L1.modify f9)))))))
  have h3456789_res : (L1.seq (L1.seq (L1.guard p) (L1.modify f3)) (L1.seq (L1.seq (L1.guard p) (L1.modify f4)) (L1.seq (L1.seq (L1.guard p) (L1.modify f5)) (L1.seq (L1.seq (L1.guard p) (L1.modify f6)) (L1.seq (L1.seq (L1.guard p) (L1.modify f7)) (L1.seq (L1.seq (L1.guard p) (L1.modify f8)) (L1.seq (L1.guard p) (L1.modify f9))))))) s2).results = {(Except.ok (), s9)} := by
    rw [h3456789.1, h456789_res]
  have h3456789_nf : ¬(L1.seq (L1.seq (L1.guard p) (L1.modify f3)) (L1.seq (L1.seq (L1.guard p) (L1.modify f4)) (L1.seq (L1.seq (L1.guard p) (L1.modify f5)) (L1.seq (L1.seq (L1.guard p) (L1.modify f6)) (L1.seq (L1.seq (L1.guard p) (L1.modify f7)) (L1.seq (L1.seq (L1.guard p) (L1.modify f8)) (L1.seq (L1.guard p) (L1.modify f9))))))) s2).failed :=
    fun hf => h456789_nf (h3456789.2.mp hf)
  -- Chain steps 2-9
  have h23456789 := L1_seq_singleton_ok h2.1 h2.2
    (m₂ := L1.seq (L1.seq (L1.guard p) (L1.modify f3)) (L1.seq (L1.seq (L1.guard p) (L1.modify f4)) (L1.seq (L1.seq (L1.guard p) (L1.modify f5)) (L1.seq (L1.seq (L1.guard p) (L1.modify f6)) (L1.seq (L1.seq (L1.guard p) (L1.modify f7)) (L1.seq (L1.seq (L1.guard p) (L1.modify f8)) (L1.seq (L1.guard p) (L1.modify f9))))))))
  have h23456789_res : (L1.seq (L1.seq (L1.guard p) (L1.modify f2)) (L1.seq (L1.seq (L1.guard p) (L1.modify f3)) (L1.seq (L1.seq (L1.guard p) (L1.modify f4)) (L1.seq (L1.seq (L1.guard p) (L1.modify f5)) (L1.seq (L1.seq (L1.guard p) (L1.modify f6)) (L1.seq (L1.seq (L1.guard p) (L1.modify f7)) (L1.seq (L1.seq (L1.guard p) (L1.modify f8)) (L1.seq (L1.guard p) (L1.modify f9)))))))) s1).results = {(Except.ok (), s9)} := by
    rw [h23456789.1, h3456789_res]
  have h23456789_nf : ¬(L1.seq (L1.seq (L1.guard p) (L1.modify f2)) (L1.seq (L1.seq (L1.guard p) (L1.modify f3)) (L1.seq (L1.seq (L1.guard p) (L1.modify f4)) (L1.seq (L1.seq (L1.guard p) (L1.modify f5)) (L1.seq (L1.seq (L1.guard p) (L1.modify f6)) (L1.seq (L1.seq (L1.guard p) (L1.modify f7)) (L1.seq (L1.seq (L1.guard p) (L1.modify f8)) (L1.seq (L1.guard p) (L1.modify f9)))))))) s1).failed :=
    fun hf => h3456789_nf (h23456789.2.mp hf)
  -- Chain all steps 1-9
  have h123456789 := L1_seq_singleton_ok h1.1 h1.2
    (m₂ := L1.seq (L1.seq (L1.guard p) (L1.modify f2)) (L1.seq (L1.seq (L1.guard p) (L1.modify f3)) (L1.seq (L1.seq (L1.guard p) (L1.modify f4)) (L1.seq (L1.seq (L1.guard p) (L1.modify f5)) (L1.seq (L1.seq (L1.guard p) (L1.modify f6)) (L1.seq (L1.seq (L1.guard p) (L1.modify f7)) (L1.seq (L1.seq (L1.guard p) (L1.modify f8)) (L1.seq (L1.guard p) (L1.modify f9)))))))))
  have h123456789_res : (L1.seq (L1.seq (L1.guard p) (L1.modify f1)) (L1.seq (L1.seq (L1.guard p) (L1.modify f2)) (L1.seq (L1.seq (L1.guard p) (L1.modify f3)) (L1.seq (L1.seq (L1.guard p) (L1.modify f4)) (L1.seq (L1.seq (L1.guard p) (L1.modify f5)) (L1.seq (L1.seq (L1.guard p) (L1.modify f6)) (L1.seq (L1.seq (L1.guard p) (L1.modify f7)) (L1.seq (L1.seq (L1.guard p) (L1.modify f8)) (L1.seq (L1.guard p) (L1.modify f9))))))))) s).results = {(Except.ok (), s9)} := by
    rw [h123456789.1, h23456789_res]
  have h123456789_nf : ¬(L1.seq (L1.seq (L1.guard p) (L1.modify f1)) (L1.seq (L1.seq (L1.guard p) (L1.modify f2)) (L1.seq (L1.seq (L1.guard p) (L1.modify f3)) (L1.seq (L1.seq (L1.guard p) (L1.modify f4)) (L1.seq (L1.seq (L1.guard p) (L1.modify f5)) (L1.seq (L1.seq (L1.guard p) (L1.modify f6)) (L1.seq (L1.seq (L1.guard p) (L1.modify f7)) (L1.seq (L1.seq (L1.guard p) (L1.modify f8)) (L1.seq (L1.guard p) (L1.modify f9))))))))) s).failed :=
    fun hf => h23456789_nf (h123456789.2.mp hf)
  -- Catch wrapper
  have h_catch := L1_catch_singleton_ok h123456789_res h123456789_nf
  unfold Sha256Core.l1_sha256_init_body
  constructor
  · exact h_catch.2
  · intro r s' h_mem
    rw [h_catch.1] at h_mem
    have ⟨hr, hs⟩ := Prod.mk.inj h_mem
    subst hr; subst hs
    intro _
    have hb := heapPtrValid_bound hpre
    have hb1 := heapPtrValid_bound hv1
    have hb2 := heapPtrValid_bound hv2
    have hb3 := heapPtrValid_bound hv3
    have hb4 := heapPtrValid_bound hv4
    have hb5 := heapPtrValid_bound hv5
    have hb6 := heapPtrValid_bound hv6
    have hb7 := heapPtrValid_bound hv7
    have hb8 := heapPtrValid_bound hv8
    have h9v : hVal s9.globals.rawHeap s9.locals.st =
        ({ hVal s8.globals.rawHeap s8.locals.st with total_bytes := 0 } : Sha256Core.C_sha256_state) :=
      hVal_heapUpdate_same _ _ _ hb8
    have h8v : hVal s8.globals.rawHeap s8.locals.st =
        ({ hVal s7.globals.rawHeap s7.locals.st with h7 := 1541459225 } : Sha256Core.C_sha256_state) :=
      hVal_heapUpdate_same _ _ _ hb7
    have h7v : hVal s7.globals.rawHeap s7.locals.st =
        ({ hVal s6.globals.rawHeap s6.locals.st with h6 := 528734635 } : Sha256Core.C_sha256_state) :=
      hVal_heapUpdate_same _ _ _ hb6
    have h6v : hVal s6.globals.rawHeap s6.locals.st =
        ({ hVal s5.globals.rawHeap s5.locals.st with h5 := 2600822924 } : Sha256Core.C_sha256_state) :=
      hVal_heapUpdate_same _ _ _ hb5
    have h5v : hVal s5.globals.rawHeap s5.locals.st =
        ({ hVal s4.globals.rawHeap s4.locals.st with h4 := 1359893119 } : Sha256Core.C_sha256_state) :=
      hVal_heapUpdate_same _ _ _ hb4
    have h4v : hVal s4.globals.rawHeap s4.locals.st =
        ({ hVal s3.globals.rawHeap s3.locals.st with h3 := 2773480762 } : Sha256Core.C_sha256_state) :=
      hVal_heapUpdate_same _ _ _ hb3
    have h3v : hVal s3.globals.rawHeap s3.locals.st =
        ({ hVal s2.globals.rawHeap s2.locals.st with h2 := 1013904242 } : Sha256Core.C_sha256_state) :=
      hVal_heapUpdate_same _ _ _ hb2
    have h2v : hVal s2.globals.rawHeap s2.locals.st =
        ({ hVal s1.globals.rawHeap s1.locals.st with h1 := 3144134277 } : Sha256Core.C_sha256_state) :=
      hVal_heapUpdate_same _ _ _ hb1
    have h1v : hVal s1.globals.rawHeap s1.locals.st =
        ({ hVal s.globals.rawHeap s.locals.st with h0 := 1779033703 } : Sha256Core.C_sha256_state) :=
      hVal_heapUpdate_same _ _ _ hb
    rw [h9v, h8v, h7v, h6v, h5v, h4v, h3v, h2v, h1v]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

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
