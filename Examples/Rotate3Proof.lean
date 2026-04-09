-- Phase 4 test: rotate3 + abs_diff + clamp verified with automation tactics
--
-- Tests the Phase 4 automation on a richer set of C functions.
-- Measures: how much of the L1corres proof is automated by corres_auto.

import Generated.Rotate3
import Clift.Lifting.SimplConv
import Clift.Tactics.CorresAuto

set_option maxHeartbeats 6400000
set_option maxRecDepth 4096

open Rotate3

/-! # L1 monadic versions -/

noncomputable def l1_rotate3_body : L1Monad ProgramState :=
  L1.catch
    (L1.seq
      (L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.a))
        (L1.modify (fun s =>
          { s with locals := { s.locals with t := hVal s.globals.rawHeap s.locals.a } })))
      (L1.seq
        (L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.a))
          (L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.b))
            (L1.modify (fun s =>
              { s with globals := { s.globals with rawHeap :=
                  (heapUpdate s.globals.rawHeap s.locals.a (hVal s.globals.rawHeap s.locals.b)) } }))))
        (L1.seq
          (L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.b))
            (L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.c))
              (L1.modify (fun s =>
                { s with globals := { s.globals with rawHeap :=
                    (heapUpdate s.globals.rawHeap s.locals.b (hVal s.globals.rawHeap s.locals.c)) } }))))
          (L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.c))
            (L1.modify (fun s =>
              { s with globals := { s.globals with rawHeap :=
                  (heapUpdate s.globals.rawHeap s.locals.c s.locals.t) } }))))))
    L1.skip

noncomputable def l1_abs_diff_body : L1Monad ProgramState :=
  L1.catch
    (L1.condition (fun s => decide (s.locals.x > s.locals.y))
      (L1.seq (L1.modify (fun s =>
        { s with locals := { s.locals with ret__val := s.locals.x - s.locals.y } })) L1.throw)
      (L1.seq (L1.modify (fun s =>
        { s with locals := { s.locals with ret__val := s.locals.y - s.locals.x } })) L1.throw))
    L1.skip

noncomputable def l1_clamp_body : L1Monad ProgramState :=
  L1.catch
    (L1.condition (fun s => decide (s.locals.val < s.locals.lo))
      (L1.seq (L1.modify (fun s =>
        { s with locals := { s.locals with ret__val := s.locals.lo } })) L1.throw)
      (L1.condition (fun s => decide (s.locals.val > s.locals.hi))
        (L1.seq (L1.modify (fun s =>
          { s with locals := { s.locals with ret__val := s.locals.hi } })) L1.throw)
        (L1.seq (L1.modify (fun s =>
          { s with locals := { s.locals with ret__val := s.locals.val } })) L1.throw)))
    L1.skip

/-! # L1corres proofs: fully automated by corres_auto -/

theorem l1_rotate3_corres :
    L1corres Rotate3.procEnv l1_rotate3_body Rotate3.rotate3_body := by
  unfold l1_rotate3_body Rotate3.rotate3_body
  corres_auto

theorem l1_abs_diff_corres :
    L1corres Rotate3.procEnv l1_abs_diff_body Rotate3.abs_diff_body := by
  unfold l1_abs_diff_body Rotate3.abs_diff_body
  corres_auto

theorem l1_clamp_corres :
    L1corres Rotate3.procEnv l1_clamp_body Rotate3.clamp_body := by
  unfold l1_clamp_body Rotate3.clamp_body
  corres_auto

/-! # Measurement: corres_auto effectiveness

    rotate3: 100% automated (catch, seq*7, guard*4, basic*4, skip)
    abs_diff: 100% automated (catch, cond, seq*2, basic*2, throw*2, skip)
    clamp: 100% automated (catch, cond*2, seq*3, basic*3, throw*3, skip)

    Total: 3/3 functions fully automated = 100% L1corres automation rate
    Zero manual proof steps required. -/

#print axioms l1_rotate3_corres
#print axioms l1_abs_diff_corres
#print axioms l1_clamp_corres
