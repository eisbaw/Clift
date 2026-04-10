# Clift Package API

## Installation

Add to your `lakefile.lean`:
```lean
require clift from git
  "https://github.com/<owner>/clift" @ "main"
```

Then `lake update && lake build`.

## Stable Public API

The following imports are considered stable and will follow semantic versioning:

### Core Framework (stable)
```lean
import Clift.MonadLib        -- NondetM, Hoare triples, corres refinement
import Clift.CSemantics      -- CSimpl, Exec, HeapRawState, CState
import Clift.Lifting         -- L1-L5 lifting stages
import Clift.Tactics         -- CVcg, SepAuto, CorresAuto, CStep
import Clift.Security        -- Integrity, confidentiality, availability, access control
import Clift.Specs           -- Reusable data structure specifications
```

### Individual Modules (stable)

#### MonadLib
- `Clift.MonadLib.NondetM` -- Nondeterministic state monad with failure
- `Clift.MonadLib.Hoare` -- Partial and total correctness Hoare triples
- `Clift.MonadLib.Corres` -- Backward simulation refinement (`corres`)

#### CSemantics
- `Clift.CSemantics.CSimpl` -- Deeply embedded imperative language
- `Clift.CSemantics.Exec` -- Big-step inductive semantics
- `Clift.CSemantics.HeapRaw` -- Byte-level heap model
- `Clift.CSemantics.CState` -- Program state (globals + locals)

#### Security
- `Clift.Security.Properties` -- Integrity, confidentiality, availability
- `Clift.Security.AccessControl` -- Generic access control framework
- `Clift.Security.Noninterference` -- Information flow security

### Experimental (may change)
- `Clift.AI` -- AI-assisted proof search integration
- `Clift.Util` -- Internal utilities
- `Clift.Security.Capabilities` -- Capability system verification pattern
- `Clift.Security.PageTable` -- Page table verification pattern
- `Clift.Security.Scheduler` -- Scheduler verification pattern
- `Clift.Security.Interrupt` -- Interrupt handling verification pattern
- `Clift.Security.FaultDelivery` -- Fault delivery verification pattern
- `Clift.Security.AuthorityConfinement` -- Authority confinement verification pattern
- `Clift.Security.Availability` -- Availability verification pattern

### Not Part of Public API
- `Generated.*` -- Output of CImporter, project-specific
- `Examples.*` -- Demonstration proofs, not for import

## Typical Usage

```lean
import Clift

-- After running CImporter on your .c file to generate CSimpl terms:
-- 1. Use L1-L5 lifting to get clean functional model
-- 2. Define AbstractSpec for your functions
-- 3. Prove refinement + functional properties
-- 4. Security properties propagate via transfer theorems
```

## Versioning Policy

- **0.x.y**: Pre-1.0, breaking changes possible in minor versions
- **1.0.0**: Stable API for MonadLib, CSemantics, Security.Properties
- Experimental modules may change without major version bump
- Lean toolchain version pinned in `lean-toolchain`

## Build Requirements

- Lean 4 (version specified in `lean-toolchain`)
- No Mathlib dependency (intentionally dropped for build performance)
- Python 3.8+ for CImporter
- clang (for `clang -Xclang -ast-dump=json`)

## Status: Ready to Publish

The package is ready for publication on reservoir.lean-lang.org. Actual publishing requires network access and a Reservoir account. The lakefile.lean is configured with version, keywords, and description for Reservoir compatibility.
