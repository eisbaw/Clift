-- Phase E test: AI-assisted spec drafting
--
-- Demonstrates the spec generation framework on ring buffer functions.
-- The mock oracle suggests FuncSpecs; the human reviews.
--
-- Reference: tasks 0101, 0103

import Clift.AI.SpecGen
import Examples.RingBufferProof

set_option maxHeartbeats 3200000

open RingBuffer

/-! # Function signature contexts for ring buffer functions -/

def rbSizeSigCtx : FuncSigContext where
  funcName := "rb_size"
  params := [{ name := "rb", cType := "rb_state *", category := .pointer, isConst := true }]
  returnType := { name := "return", cType := "unsigned int", category := .scalar, isConst := false }
  docComment := some "Returns the number of elements in the ring buffer."
  modifiesHeap := false

def rbIsEmptySigCtx : FuncSigContext where
  funcName := "rb_is_empty"
  params := [{ name := "rb", cType := "rb_state *", category := .pointer, isConst := true }]
  returnType := { name := "return", cType := "int", category := .scalar, isConst := false }
  docComment := some "Returns 1 if the ring buffer is empty, 0 otherwise."
  modifiesHeap := false

def rbPushSigCtx : FuncSigContext where
  funcName := "rb_push"
  params := [
    { name := "rb", cType := "rb_state *", category := .pointer, isConst := false },
    { name := "value", cType := "unsigned int", category := .scalar, isConst := false }
  ]
  returnType := { name := "return", cType := "int", category := .scalar, isConst := false }
  docComment := some "Pushes a value onto the ring buffer. Returns 0 on success, -1 if full."
  modifiesHeap := true

def rbCapacitySigCtx : FuncSigContext where
  funcName := "rb_capacity"
  params := [{ name := "rb", cType := "rb_state *", category := .pointer, isConst := true }]
  returnType := { name := "return", cType := "unsigned int", category := .scalar, isConst := false }
  docComment := some "Returns the maximum capacity of the ring buffer."
  modifiesHeap := false

def rbIsFullSigCtx : FuncSigContext where
  funcName := "rb_is_full"
  params := [{ name := "rb", cType := "rb_state *", category := .pointer, isConst := true }]
  returnType := { name := "return", cType := "int", category := .scalar, isConst := false }
  docComment := some "Returns 1 if the ring buffer is full, 0 otherwise."
  modifiesHeap := false

/-! # "AI-suggested" FuncSpecs -/

def aiRbSizeSpec : SpecSuggestion RingBuffer.ProgramState :=
  { spec := rb_size_spec
    preDescription := "rb pointer is heap-valid"
    postDescription := "return value equals rb->count"
    confidence := 0.9 }

def aiRbIsEmptySpec : SpecSuggestion RingBuffer.ProgramState :=
  { spec := rb_is_empty_spec
    preDescription := "rb pointer is heap-valid"
    postDescription := "return 1 iff count = 0"
    confidence := 0.85 }

def aiRbIsFullSpec : SpecSuggestion RingBuffer.ProgramState :=
  { spec := rb_is_full_spec
    preDescription := "rb pointer is heap-valid"
    postDescription := "return 1 iff count >= capacity"
    confidence := 0.85 }

def aiRbCapacitySpec : SpecSuggestion RingBuffer.ProgramState :=
  { spec := rb_capacity_spec
    preDescription := "rb pointer is heap-valid"
    postDescription := "return value equals rb->capacity"
    confidence := 0.9 }

/-! # Mock spec oracle -/

def rbSpecOracle : SpecOracle RingBuffer.ProgramState :=
  mkMockSpecOracle [
    ("rb_size", [aiRbSizeSpec]),
    ("rb_is_empty", [aiRbIsEmptySpec]),
    ("rb_is_full", [aiRbIsFullSpec]),
    ("rb_capacity", [aiRbCapacitySpec])
  ]

/-! # Pattern-based analysis tests -/

theorem rb_size_has_pointer_param :
    pointerParamNames rbSizeSigCtx = ["rb"] := by native_decide

theorem rb_size_is_read_only :
    isReadOnly rbSizeSigCtx = true := by native_decide

theorem rb_push_not_read_only :
    isReadOnly rbPushSigCtx = false := by native_decide

theorem rb_push_has_return :
    hasReturnValue rbPushSigCtx = true := by native_decide

/-! # Oracle query tests -/

theorem rb_size_oracle_responds :
    (rbSpecOracle.suggest rbSizeSigCtx).length > 0 := by native_decide

theorem rb_is_empty_oracle_responds :
    (rbSpecOracle.suggest rbIsEmptySigCtx).length > 0 := by native_decide

theorem unknown_func_no_suggestion :
    (rbSpecOracle.suggest {
      funcName := "unknown_func"
      params := []
      returnType := { name := "return", cType := "void", category := .void, isConst := false }
      docComment := none
      modifiesHeap := false
    }).length = 0 := by native_decide

/-! # Metrics

## Spec generation results (mock oracle)

| Function      | Suggested | Matches Human | Confidence |
|---------------|-----------|---------------|------------|
| rb_size       | Yes       | Exact match   | 0.9        |
| rb_is_empty   | Yes       | Exact match   | 0.85       |
| rb_is_full    | Yes       | Exact match   | 0.85       |
| rb_capacity   | Yes       | Exact match   | 0.9        |
| rb_push       | No (mock) | N/A           | N/A        |

First-shot acceptance rate: 4/5 = 80%
-/

-- Axiom audit
#print axioms rb_size_has_pointer_param
#print axioms rb_size_is_read_only
#print axioms rb_push_not_read_only
#print axioms rb_size_oracle_responds
#print axioms unknown_func_no_suggestion
