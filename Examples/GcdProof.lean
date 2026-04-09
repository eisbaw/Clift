-- Phase 1 end-to-end: gcd.c through L1 lifting with L1corres proof
--
-- Pipeline: Generated/Gcd.lean (CSimpl) -> L1 monadic form -> L1corres proof
-- This demonstrates the L1 lifting stage of the verification pipeline.

import Generated.Gcd
import Clift.Lifting.SimplConv

set_option maxHeartbeats 1600000

open Gcd

/-! # L1 monadic version of gcd -/

/-- L1 monadic version of gcd_body.
    This is the manual translation following the CSimpl structure:
    catch (seq (while ...) (seq (basic ret_val := a) throw)) skip

    In Phase 2, this will be generated automatically by MetaM. -/
def l1_gcd_body : L1Monad ProgramState :=
  L1.catch
    (L1.seq
      (L1.while (fun s => decide (s.locals.b ≠ 0))
        (L1.seq
          (L1.modify (fun s => { s with locals := { s.locals with t := s.locals.b } }))
          (L1.seq
            (L1.seq (L1.guard (fun s => s.locals.b ≠ 0))
              (L1.modify (fun s => { s with locals := { s.locals with b := (s.locals.a % s.locals.b) } })))
            (L1.modify (fun s => { s with locals := { s.locals with a := s.locals.t } })))))
      (L1.seq
        (L1.modify (fun s => { s with locals := { s.locals with ret__val := s.locals.a } }))
        L1.throw))
    L1.skip

/-! # L1corres proof: l1_gcd_body corresponds to gcd_body -/

/-- L1corres for gcd: the L1 monadic version faithfully represents the CSimpl body. -/
theorem l1_gcd_body_corres :
    L1corres Gcd.procEnv l1_gcd_body Gcd.gcd_body := by
  unfold l1_gcd_body Gcd.gcd_body
  apply L1corres_catch
  · apply L1corres_seq
    · apply L1corres_while
      apply L1corres_seq
      · exact L1corres_basic _ _
      · apply L1corres_seq
        · exact L1corres_guard _ (L1corres_basic _ _)
        · exact L1corres_basic _ _
    · apply L1corres_seq
      · exact L1corres_basic _ _
      · exact L1corres_throw _
  · exact L1corres_skip _
