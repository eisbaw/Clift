-- Task 0156: seL4 capability operations verification
--
-- Real-world target: seL4 kernel bitfield manipulation functions.
-- 6 functions imported from sel4_cap.c (~60 LOC C -> ~126 lines Lean).
--
-- Key verification targets:
-- - Capability type extraction correctness
-- - Pointer extraction mask correctness
-- - Object type classification range check
-- - Null capability detection
-- - Capability equality
-- - Lookup fault computation

import Generated.Sel4Cap
import Clift.Lifting.Pipeline
import Clift.Lifting.FuncSpec

set_option maxHeartbeats 12800000
set_option maxRecDepth 4096

open Sel4Cap

/-! # Step 1: Run the clift pipeline on all 6 functions -/

clift Sel4Cap

/-! # Step 2: Verify L1 definitions exist -/

#check @Sel4Cap.l1_cap_get_capType_body
#check @Sel4Cap.l1_cap_get_capPtr_body
#check @Sel4Cap.l1_isArchObjectType_body
#check @Sel4Cap.l1_cap_is_null_body
#check @Sel4Cap.l1_cap_equal_body
#check @Sel4Cap.l1_lookup_fault_depth_mismatch_body

/-! # Step 3: FuncSpecs for seL4 capability operations -/

/-- cap_get_capType: extracts bits [28:24] from w0.
    Pure bitfield extraction. Spec IS the seL4 definition. -/
def cap_get_capType_spec : FuncSpec ProgramState where
  pre := fun _ => True
  post := fun r s =>
    r = Except.ok () →
    s.locals.ret__val = (s.locals.w0 >>> 24) &&& 0x1F

/-- cap_get_capPtr: extracts lower 24 bits from w0. -/
def cap_get_capPtr_spec : FuncSpec ProgramState where
  pre := fun _ => True
  post := fun r s =>
    r = Except.ok () →
    s.locals.ret__val = s.locals.w0 &&& 0x00FFFFFF

/-- isArchObjectType: checks type in [16, 31]. -/
def isArchObjectType_spec : FuncSpec ProgramState where
  pre := fun _ => True
  post := fun r s =>
    r = Except.ok () →
    (s.locals.type >= 16 ∧ s.locals.type <= 31 →
      s.locals.ret__val = 1) ∧
    (¬(s.locals.type >= 16 ∧ s.locals.type <= 31) →
      s.locals.ret__val = 0)

/-- cap_is_null: checks if type field is 0. -/
def cap_is_null_spec : FuncSpec ProgramState where
  pre := fun _ => True
  post := fun r s =>
    r = Except.ok () →
    ((s.locals.w0 >>> 24) &&& 0x1F = 0 → s.locals.ret__val = 1) ∧
    ((s.locals.w0 >>> 24) &&& 0x1F ≠ 0 → s.locals.ret__val = 0)

/-- cap_equal: both words must match. -/
def cap_equal_spec : FuncSpec ProgramState where
  pre := fun _ => True
  post := fun r s =>
    r = Except.ok () →
    (s.locals.w0a = s.locals.w0b ∧ s.locals.w1a = s.locals.w1b →
      s.locals.ret__val = 1) ∧
    (¬(s.locals.w0a = s.locals.w0b ∧ s.locals.w1a = s.locals.w1b) →
      s.locals.ret__val = 0)

/-- lookup_fault_depth_mismatch: remaining bits. -/
def lookup_fault_depth_mismatch_spec : FuncSpec ProgramState where
  pre := fun _ => True
  post := fun r s =>
    r = Except.ok () →
    (s.locals.bitsFound >= s.locals.bitsNeeded →
      s.locals.ret__val = 0) ∧
    (s.locals.bitsFound < s.locals.bitsNeeded →
      s.locals.ret__val = s.locals.bitsNeeded - s.locals.bitsFound)

/-! # Step 4: validHoare theorems -/

theorem cap_get_capType_correct :
    cap_get_capType_spec.satisfiedBy Sel4Cap.l1_cap_get_capType_body := by
  sorry

theorem cap_get_capPtr_correct :
    cap_get_capPtr_spec.satisfiedBy Sel4Cap.l1_cap_get_capPtr_body := by
  sorry

theorem isArchObjectType_correct :
    isArchObjectType_spec.satisfiedBy Sel4Cap.l1_isArchObjectType_body := by
  sorry

theorem cap_is_null_correct :
    cap_is_null_spec.satisfiedBy Sel4Cap.l1_cap_is_null_body := by
  sorry

theorem lookup_fault_depth_mismatch_correct :
    lookup_fault_depth_mismatch_spec.satisfiedBy
      Sel4Cap.l1_lookup_fault_depth_mismatch_body := by
  sorry

/-! # Step 5: Gap analysis

seL4 C features not handled by Clift:
1. Struct arrays (word_t words[2] in cap_t) - CImporter limitation
2. Static inline / function calls in expressions - CImporter limitation
3. 64-bit operations (seL4 uses uint64_t caps) - Clift focuses on uint32_t
4. Bitfield struct DSL (seL4 generates C from BF specs) - not supported
5. Function pointers (seL4 syscall dispatch) - not supported
6. Complement operator (~~~) type inference issue - CImporter bug

Status: 6 core functions imported + lifted to L1, 6 FuncSpecs written,
5 validHoare theorems stated (sorry).
-/
