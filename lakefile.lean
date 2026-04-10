import Lake
open Lake DSL

package clift where
  version := v!"0.1.0"
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]
  keywords := #["formal-verification", "c-verification", "refinement", "seL4", "autocorres"]
  description := "Lifting C into Lean 4 for formal verification, following seL4's AutoCorres methodology"

-- Core library: monadic foundations + C semantics + lifting + tactics
@[default_target]
lean_lib Clift where
  srcDir := "."

-- Generated CSimpl definitions (output of CImporter, version controlled)
@[default_target]
lean_lib Generated where
  roots := #[`Generated.Max, `Generated.Gcd, `Generated.Swap, `Generated.ListLength, `Generated.Rotate3,
             `Generated.DivTest, `Generated.SignedArith, `Generated.ForLoop, `Generated.DoWhile, `Generated.SwitchTest,
             `Generated.MultiCall, `Generated.RingBuffer, `Generated.SumArray,
             `Generated.EnumTypedefGlobal,
             `Generated.RingBufferExt,
             `Generated.Bitwise,
             `Generated.CastsSizeof,
             `Generated.MultiProject.Types,
             `Generated.MultiProject.Helper,
             `Generated.MultiProject.Main,
             `Generated.UnionsVoid,
             `Generated.Strings,
             `Generated.RtosQueue,
             `Generated.Sha256Core,
             `Generated.UartDriver,
             `Generated.PacketParser,
             `Generated.Sel4Cap,
             `Generated.HashTable,
             `Generated.MemAlloc,
             `Generated.Rbtree,
             `Generated.StateMachine,
             `Generated.PriorityQueue,
             `Generated.DmaBuffer]

-- User proof examples
@[default_target]
lean_lib Examples where
  roots := #[`Examples.MaxProof, `Examples.MetaMTest, `Examples.Benchmark,
             `Examples.GcdProof, `Examples.GcdCorrect, `Examples.GcdTypeStrengthen,
             `Examples.GcdWordAbstract, `Examples.GcdPhase2,
             `Examples.GcdL2,
             `Examples.SwapProof, `Examples.SwapHeapLift,
             `Examples.SwapL2,
             `Examples.Rotate3Proof,
             `Examples.L1AutoTest,
             `Examples.PipelineTest,
             `Examples.MultiCallProof,
             `Examples.ListLengthProof,
             `Examples.RingBufferProof,
             `Examples.AIInvariantTest,
             `Examples.AIStructInvariantTest,
             `Examples.AISpecTest,
             `Examples.PhaseEMilestone,
             `Examples.L1VcgTest,
             `Examples.RingBufferExtProof,
             `Examples.SoundnessCheck,
             `Examples.TerminationProofs,
             `Examples.RBExtFuncSpecs,
             `Examples.RBExtRefinement,
             `Examples.AxiomAudit,
             `Examples.ExecAudit,
             `Examples.SorryAudit,
             `Examples.SystemCorrectness,
             `Examples.RtosQueueProof,
             `Examples.Sha256CoreProof,
             `Examples.UartDriverProof,
             `Examples.PacketParserProof,
             `Examples.Sel4CapProof,
             `Examples.HashTableProof,
             `Examples.MemAllocProof,
             `Examples.RbtreeProof,
             `Examples.StateMachineProof,
             `Examples.PriorityQueueProof,
             `Examples.DmaBufferProof,
             `Examples.SpecCompletenessReview,
             `Examples.ArrayBoundsProof]
