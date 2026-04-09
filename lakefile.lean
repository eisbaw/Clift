import Lake
open Lake DSL

package clift where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

-- Pin Mathlib (exact commit managed by lake-manifest.json)
require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

-- Core library: monadic foundations + C semantics + lifting + tactics
@[default_target]
lean_lib Clift where
  srcDir := "."

-- Generated CSimpl definitions (output of CImporter, version controlled)
@[default_target]
lean_lib Generated where
  roots := #[`Generated.Max, `Generated.Gcd]

-- User proof examples
@[default_target]
lean_lib Examples where
  roots := #[`Examples.MaxProof, `Examples.MetaMTest, `Examples.Benchmark,
             `Examples.GcdProof, `Examples.GcdCorrect, `Examples.GcdTypeStrengthen,
             `Examples.GcdWordAbstract, `Examples.GcdPhase2]
