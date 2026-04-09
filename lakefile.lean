import Lake
open Lake DSL

package clift where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

-- Core library: monadic foundations + C semantics + lifting + tactics
@[default_target]
lean_lib Clift where
  srcDir := "."

-- Generated CSimpl definitions (output of CImporter, version controlled)
@[default_target]
lean_lib Generated where
  roots := #[`Generated.Max, `Generated.Gcd, `Generated.Swap, `Generated.ListLength]

-- User proof examples
@[default_target]
lean_lib Examples where
  roots := #[`Examples.MaxProof, `Examples.MetaMTest, `Examples.Benchmark,
             `Examples.GcdProof, `Examples.GcdCorrect, `Examples.GcdTypeStrengthen,
             `Examples.GcdWordAbstract, `Examples.GcdPhase2,
             `Examples.SwapProof]
