-- RAG index over proven lemmas for proof retrieval
--
-- A simple index mapping goal patterns to proof scripts.
-- When AI faces a new proof goal, it retrieves the most similar
-- previously-proven goals and uses them as few-shot examples.
--
-- This is deliberately simple: a list of (pattern, proof) pairs
-- with string-based matching. A real implementation would use
-- embeddings, but the architecture is the same.
--
-- Reference: task-0102

import Clift.Lifting.L1HoareRules

/-! # Proof entry: a proven goal with its proof script -/

/-- A single entry in the proof index.
    Maps a goal pattern to a proof approach. -/
structure ProofEntry where
  /-- Goal pattern (human-readable description of the goal shape) -/
  goalPattern : String
  /-- Tags for categorization (e.g., "while", "hoare", "sep-logic") -/
  tags : List String
  /-- The proof script that worked (tactic sequence as string) -/
  proofScript : String
  /-- Key lemmas used in the proof -/
  keyLemmas : List String
  /-- Notes on when this proof pattern applies -/
  applicabilityNotes : String

/-! # Proof index: collection of proven goals -/

/-- The proof index: a searchable collection of proof entries.
    In a real system this would be backed by an embedding store.
    Here it is a simple list with tag-based filtering. -/
structure ProofIndex where
  /-- All entries -/
  entries : List ProofEntry

/-- Create an empty proof index. -/
def ProofIndex.empty : ProofIndex := { entries := [] }

/-- Add an entry to the index. -/
def ProofIndex.add (idx : ProofIndex) (entry : ProofEntry) : ProofIndex :=
  { entries := entry :: idx.entries }

/-- Search by tag: return entries matching any of the given tags. -/
def ProofIndex.searchByTag (idx : ProofIndex) (tags : List String) : List ProofEntry :=
  idx.entries.filter fun e => tags.any fun t => e.tags.contains t

/-- Search by keyword in goal pattern. -/
def ProofIndex.searchByKeyword (idx : ProofIndex) (keyword : String) : List ProofEntry :=
  idx.entries.filter fun e =>
    let parts := e.goalPattern.splitOn keyword
    parts.length > 1

/-- Retrieve top-N entries by relevance (tag match count). -/
def ProofIndex.topN (idx : ProofIndex) (tags : List String) (n : Nat) : List ProofEntry :=
  let scored := idx.entries.map fun e =>
    let score := tags.foldl (fun acc t => if e.tags.contains t then acc + 1 else acc) 0
    (score, e)
  let sorted := scored.filter (fun (s, _) => s > 0)
  -- Take first n (already partially sorted by insertion order)
  (sorted.take n).map Prod.snd

/-! # Built-in proof index for Clift

These entries capture the proof patterns used in our verified examples.
An LLM retriever would use these as few-shot examples. -/

/-- The Clift proof index with entries from all verified examples. -/
def cliftProofIndex : ProofIndex := ProofIndex.empty
  |>.add {
    goalPattern := "validHoare P (L1.while cond body) Q"
    tags := ["while", "loop", "invariant", "hoare"]
    proofScript := "apply while_invariant_rule with inv; prove h_init, h_pres, h_exit"
    keyLemmas := ["while_invariant_rule", "wp_while_sound"]
    applicabilityNotes := "Use for any while loop. Requires finding a loop invariant."
  }
  |>.add {
    goalPattern := "validHoare P (L1.seq m1 m2) Q"
    tags := ["seq", "hoare", "sequential"]
    proofScript := "apply L1_hoare_seq with mid-condition; prove both halves"
    keyLemmas := ["L1_hoare_seq", "wp_seq_sound"]
    applicabilityNotes := "Sequential composition. Find the intermediate condition."
  }
  |>.add {
    goalPattern := "validHoare P (L1.modify f) Q"
    tags := ["modify", "hoare", "assignment"]
    proofScript := "apply L1_hoare_modify; simplify postcondition at (f s)"
    keyLemmas := ["L1_hoare_modify", "wp_modify_sound"]
    applicabilityNotes := "Simple state update. Q must hold at (f s) when P holds at s."
  }
  |>.add {
    goalPattern := "validHoare P (L1.guard p) Q"
    tags := ["guard", "hoare", "assertion"]
    proofScript := "apply L1_hoare_guard; prove p s and Q (ok ()) s from P s"
    keyLemmas := ["L1_hoare_guard", "wp_guard_sound"]
    applicabilityNotes := "Guard check. P must imply both (p s) and Q."
  }
  |>.add {
    goalPattern := "validHoare P (L1.catch body handler) Q"
    tags := ["catch", "hoare", "exception"]
    proofScript := "apply L1_hoare_catch with mid; prove body and handler"
    keyLemmas := ["L1_hoare_catch", "wp_catch_sound"]
    applicabilityNotes := "Exception handling. OK results pass through, errors go to handler."
  }
  |>.add {
    goalPattern := "preserves_invariant inv body pre post"
    tags := ["invariant", "preservation", "global"]
    proofScript := "intro s h_inv_and_pre; unfold body; split on cases"
    keyLemmas := ["preserves_invariant", "preserves_from_funcSpec"]
    applicabilityNotes := "Struct invariant preservation. Show inv held before implies inv after."
  }
  |>.add {
    goalPattern := "mapsTo p v heap -> mapsTo p v (heapUpdate heap q w)"
    tags := ["sep-logic", "frame", "heap", "pointer"]
    proofScript := "apply mapsTo_heapUpdate_other; prove p != q"
    keyLemmas := ["mapsTo_heapUpdate_other", "frame_rule"]
    applicabilityNotes := "Frame rule for disjoint pointers. Need to show addresses differ."
  }
  |>.add {
    goalPattern := "isList p xs heap"
    tags := ["linked-list", "heap", "recursive"]
    proofScript := "induction xs; apply isList.nil; apply isList.cons with validity proofs"
    keyLemmas := ["isList.nil", "isList.cons", "isList_null", "isList_nonnull"]
    applicabilityNotes := "Linked list predicate. Induction on the list or the pointer chain."
  }
  |>.add {
    goalPattern := "opRefinement absOp concreteBody R"
    tags := ["refinement", "abstract-spec", "simulation"]
    proofScript := "apply funcSpec_implies_refinement with fspec; prove pre/post bridges"
    keyLemmas := ["funcSpec_implies_refinement", "refinement_transfers_property"]
    applicabilityNotes := "Refinement proof connecting C to abstract spec via simulation."
  }
  |>.add {
    goalPattern := "UInt32.toNat arithmetic"
    tags := ["arithmetic", "uint32", "overflow"]
    proofScript := "rw [UInt32.toNat_add]; apply Nat.mod_eq_of_lt; omega"
    keyLemmas := ["UInt32.toNat_add", "Nat.mod_eq_of_lt"]
    applicabilityNotes := "UInt32 arithmetic. Show no overflow, then reduce to Nat."
  }

/-! # Usage: how ai_prove would use the index

The workflow for AI-assisted proof:
1. Parse the current goal into tags (e.g., "validHoare", "while", etc.)
2. Query cliftProofIndex.topN with those tags
3. Include retrieved proof scripts in the LLM prompt as few-shot examples
4. LLM generates a proof attempt
5. Lean kernel checks the proof
6. On success, add the new proof to the index
7. On failure, retry with different examples or ask the human
-/
