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
lean_lib Generated where
  srcDir := "Generated"

-- User proof examples
lean_lib Examples where
  srcDir := "Examples"
