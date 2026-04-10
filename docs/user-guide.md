# Clift User Guide: Verifying C Code with Lean 4

## Quick Start

Verify your first C function in 30 minutes.

### Prerequisites

- Git
- Nix (with flakes enabled)
- A C function you want to verify

### Step 1: Set Up the Environment

```bash
git clone <clift-repo-url>
cd clift

# Enter the Nix development shell (provides lean, lake, clang, python3)
nix develop

# Build the Clift library
lake build Clift
```

If this is your first build, it will take several minutes to compile the Lean
library. Subsequent builds are incremental.

### Step 2: Write a C Function

Create a C file, for example `test/c_sources/my_max.c`:

```c
#include <stdint.h>

uint32_t my_max(uint32_t a, uint32_t b) {
    if (a > b) {
        return a;
    } else {
        return b;
    }
}
```

**Supported C subset** (StrictC restrictions):
- Integer types: `uint8_t`, `uint16_t`, `uint32_t`, `uint64_t`, `int32_t`, etc.
- Pointers: `T*`, `void*`, struct pointers
- Structs, enums, typedefs, unions
- Control flow: `if/else`, `while`, `for`, `do-while`, `switch`
- Bitwise operations: `&`, `|`, `^`, `~`, `<<`, `>>`
- Casts, `sizeof`, global variables
- Multi-file projects

**Not supported** (will cause import errors):
- Floating point
- `goto`, `longjmp`, switch fall-through
- Address-of local variables (`&local_var`)
- Variadic functions, VLAs
- Side effects in expressions
- `malloc`/`free` (use external allocator pattern)

### Step 3: Run CImporter

```bash
# Import the C file into Lean
just import test/c_sources/my_max.c MyMax
```

This creates `Generated/MyMax.lean` containing:
- `structure ProgramState` -- the C program's state (globals + locals)
- `def my_max_body : CSimpl ProgramState` -- the deeply embedded C function
- `def procEnv : ProcEnv ProgramState` -- procedure environment

Open `Generated/MyMax.lean` to inspect the generated code. Each C statement
is represented as a `CSimpl` constructor (`seq`, `cond`, `basic`, etc.).

### Step 4: Register the Module

Add the new module to `lakefile.lean`:

```lean
lean_lib Generated where
  roots := #[..., `Generated.MyMax]
```

### Step 5: Run the Lifting Pipeline

Create `Examples/MyMaxProof.lean`:

```lean
import Generated.MyMax
import Clift.Lifting.Pipeline
import Clift.Lifting.FuncSpec

open MyMax

-- Run the automated lifting pipeline
clift MyMax

-- Verify the pipeline generated L1/L2/L3 forms
#check @MyMax.l1_my_max_body           -- L1 monadic form
#check @MyMax.l1_my_max_body_corres    -- L1 correspondence proof
#check @MyMax.l2_my_max_body           -- L2 extracted form
#check @MyMax.l3_my_max_body_level     -- L3 monad classification
```

Build to verify everything compiles:

```bash
lake build
```

### Step 6: Write a FuncSpec

A `FuncSpec` declares what the function should do:

```lean
/-- my_max returns the larger of its two arguments. -/
def my_max_spec : FuncSpec ProgramState where
  pre := fun _ => True   -- no precondition
  post := fun r s =>
    r = Except.ok () ->   -- normal return
    (s.locals.a >= s.locals.b -> s.locals.ret__val = s.locals.a) /\
    (s.locals.a < s.locals.b -> s.locals.ret__val = s.locals.b)
```

### Step 7: Prove It

Prove the function satisfies its spec by establishing a Hoare triple:

```lean
theorem my_max_correct :
    my_max_spec.satisfiedBy l1_my_max_body := by
  intro s0 h_pre
  -- Unfold the L1 body and apply Hoare rules
  -- ... (proof steps depend on the function)
  sorry  -- replace with actual proof
```

For simple functions, the VCG tactic can automate this:

```lean
theorem my_max_correct :
    my_max_spec.satisfiedBy l1_my_max_body := by
  intro s0 h_pre
  simp [my_max_spec, FuncSpec.satisfiedBy, validHoare] at *
  -- Use omega, simp, decide for arithmetic goals
  sorry
```

For complex proofs, use the AI proof engine:

```bash
just prove Examples/MyMaxProof.lean
```

### Step 8: Run End-to-End Tests

```bash
just e2e
```

This runs all CImporter tests, snapshot tests, and builds all Lean code.


## Worked Example: Bounded Counter Module (100 LOC)

Here is a complete walkthrough verifying a bounded counter module from scratch.

### The C Code

File: `test/c_sources/counter.c` (42 LOC)

```c
#include <stdint.h>

struct counter_state {
    uint32_t value;
    uint32_t max_value;
    uint32_t total_increments;
    uint32_t total_decrements;
};

/* Initialize counter with given maximum */
uint32_t counter_init(struct counter_state *cs, uint32_t max_val) {
    cs->value = 0;
    cs->max_value = max_val;
    cs->total_increments = 0;
    cs->total_decrements = 0;
    return 0;
}

/* Increment counter, returns 1 if at max (no change), 0 on success */
uint32_t counter_increment(struct counter_state *cs) {
    if (cs->value >= cs->max_value) {
        return 1;
    }
    cs->value = cs->value + 1;
    cs->total_increments = cs->total_increments + 1;
    return 0;
}

/* Decrement counter, returns 1 if at zero (no change), 0 on success */
uint32_t counter_decrement(struct counter_state *cs) {
    if (cs->value == 0) {
        return 1;
    }
    cs->value = cs->value - 1;
    cs->total_decrements = cs->total_decrements + 1;
    return 0;
}

/* Get current value */
uint32_t counter_get_value(struct counter_state *cs) {
    return cs->value;
}

/* Reset counter to zero */
uint32_t counter_reset(struct counter_state *cs) {
    cs->value = 0;
    return 0;
}
```

### Step 1: Import

```bash
just import test/c_sources/counter.c Counter
```

### Step 2: Register in lakefile.lean

Add `Generated.Counter` to the roots list.

### Step 3: Create Proof File

File: `Examples/CounterProof.lean`

```lean
import Generated.Counter
import Clift.Lifting.Pipeline
import Clift.Lifting.FuncSpec
import Clift.Lifting.AbstractSpec
import Clift.Lifting.GlobalInvariant

open Counter

-- Run the full pipeline
clift Counter

-- Define the abstract specification
namespace CounterSpec

structure CounterState where
  value : Nat
  maxValue : Nat
  totalIncrements : Nat
  totalDecrements : Nat

inductive CounterOp where
  | init (maxVal : Nat)
  | increment
  | decrement
  | getValue
  | reset

def counterSpec : AbstractSpec CounterState CounterOp where
  init := fun s => s.value = 0 /\ s.maxValue > 0 /\
                   s.totalIncrements = 0 /\ s.totalDecrements = 0
  opSpec := fun op => match op with
    | .init maxVal => {
        pre := fun _ => maxVal > 0
        post := fun _ s' => s'.value = 0 /\ s'.maxValue = maxVal /\
                            s'.totalIncrements = 0 /\ s'.totalDecrements = 0
      }
    | .increment => {
        pre := fun s => s.value < s.maxValue
        post := fun s s' => s'.value = s.value + 1 /\
                            s'.maxValue = s.maxValue /\
                            s'.totalIncrements = s.totalIncrements + 1
      }
    | .decrement => {
        pre := fun s => s.value > 0
        post := fun s s' => s'.value = s.value - 1 /\
                            s'.maxValue = s.maxValue /\
                            s'.totalDecrements = s.totalDecrements + 1
      }
    | .getValue => {
        pre := fun _ => True
        post := fun s s' => s' = s
      }
    | .reset => {
        pre := fun _ => True
        post := fun s s' => s'.value = 0 /\ s'.maxValue = s.maxValue
      }
  inv := fun s => s.value <= s.maxValue /\ s.maxValue > 0

-- Key property: increment followed by decrement is identity on value
theorem inc_dec_identity (s s1 s2 : CounterState)
    (h_inv : counterSpec.inv s)
    (h_inc : (counterSpec.opSpec .increment).post s s1)
    (h_dec : (counterSpec.opSpec .decrement).post s1 s2) :
    s2.value = s.value := by
  obtain ⟨h1, _, _⟩ := h_inc
  obtain ⟨h2, _, _⟩ := h_dec
  omega

-- Key property: value never exceeds max
theorem value_bounded (s s' : CounterState) (op : CounterOp)
    (h_inv : counterSpec.inv s)
    (h_pre : (counterSpec.opSpec op).pre s)
    (h_post : (counterSpec.opSpec op).post s s') :
    s'.value <= s'.maxValue := by
  cases op <;> simp [counterSpec] at h_post ⊢ <;> obtain ⟨h_val, h_max, _⟩ := h_inv
  all_goals omega

end CounterSpec
```

### Step 4: Build and Verify

```bash
lake build
```

If the build succeeds with no errors and no sorry, every theorem is
kernel-checked by Lean 4.


## The Verification Pipeline in Detail

```
C source (.c)
    |  clang -Xclang -ast-dump=json
    v
[Stage 0: CImporter]       Python: reads JSON, emits .lean
    |  CSimpl terms (deeply embedded imperative language)
    v
[Stage 1: clift_l1]        CSimpl -> L1 monadic form + L1corres proof
    |  Shallow monadic embedding
    v
[Stage 2: clift_l2]        L1 -> L2: locals become lambda-bound variables
    |  Eliminates the ugly shared-locals record
    v
[Stage 3: clift_l3]        L2 -> L3: classify monad level (pure/nondet)
    |  Tightest monad per function
    v
[User writes specs]        FuncSpec + AbstractSpec
    |  Prove FuncSpec.satisfiedBy for each function
    v
[Properties proved]        Correctness chains back to C via corres lemmas
```

Each stage produces a correspondence proof that the transformation preserves
all behaviors. The proofs compose: a property proved at the spec level
automatically holds for the original C code.


## Writing Specifications

### FuncSpec (per-function)

A `FuncSpec` is a Hoare triple `{pre} body {post}`:

```lean
def my_func_spec : FuncSpec ProgramState where
  pre := fun s =>
    -- Precondition: what must hold before calling the function
    heapPtrValid s.globals.rawHeap s.locals.ptr_arg
  post := fun r s =>
    -- Postcondition: what holds after the function returns
    r = Except.ok () ->  -- on normal return
    s.locals.ret__val = expected_value
```

Guidelines:
- `pre` should capture all pointer validity requirements
- `post` should describe the return value AND state changes
- Use `r = Except.ok ()` to restrict to normal returns
- Use `r = Except.error ()` for error/early-return paths

### AbstractSpec (system-level)

An `AbstractSpec` describes the whole module's behavior:

```lean
structure AbstractSpec (S : Type) (Op : Type) where
  init : S -> Prop                    -- valid initial states
  opSpec : Op -> OpSpec S             -- per-operation pre/post
  inv : S -> Prop                     -- system invariant
```

Guidelines:
- The abstract state should be "obviously correct" -- use Lean types
  like `List`, `Nat`, `Option` instead of `UInt32` or pointers
- The invariant should capture all important relationships between
  state components
- Prove abstract properties FIRST, then connect to C via refinement

### Connecting FuncSpec to AbstractSpec

Use `funcSpec_implies_refinement` to bridge the gap:

1. Define a simulation relation `R : C -> S -> Prop`
2. Prove each FuncSpec implies the corresponding refinement
3. Properties proved on the abstract spec transfer to C for free


## Common Errors and Troubleshooting

### "unknown identifier 'ProgramState'"

The generated module hasn't been imported. Add:
```lean
import Generated.MyModule
open MyModule
```

### "maximum heartbeat count exceeded"

The proof search is taking too long. Options:
```lean
set_option maxHeartbeats 800000  -- increase limit
```
Or break the proof into smaller lemmas.

### CImporter fails with "unsupported node type"

The C code uses a feature not in the supported subset. Check:
- No floating point
- No goto/longjmp
- No address-of local variables
- No variadic functions
- No side effects in expressions (e.g., `a++ + b++`)

### "sorry found in proof"

A proof obligation is incomplete. Either:
1. Complete the proof manually
2. Use `just prove <file>` to try AI proof
3. Check if the spec is too strong (impossible to prove)

### lake build hangs

Check for runaway processes:
```bash
ps aux | grep -E "lean|lake" | grep -v grep
```
Kill stale processes and retry.

### Struct field access generates wrong offsets

Run the struct layout test:
```bash
just test-struct-layout
```
If it fails, the CImporter's struct layout doesn't match gcc's.
Check for padding/alignment issues.

### "kernel got stuck" or deep recursion errors

```lean
set_option maxRecDepth 4096  -- increase recursion limit
```

### Multi-file project: "unknown identifier from other module"

For multi-file C projects, use:
```bash
just multi-import ProjectName file1.c file2.c
```
This generates separate .lean files with cross-module imports.


## Project Structure

```
clift/
  Clift/                    -- Core library
    MonadLib/               -- NondetM, Hoare triples, corres
    CSemantics/             -- CSimpl, Exec, CState, HeapRawState
    Lifting/                -- Pipeline stages (L1-L5)
    Tactics/                -- CVcg, SepAuto, CorresAuto, CStep
    AI/                     -- AI-assisted proof generation
    Security/               -- Integrity, confidentiality, availability
    Specs/                  -- Reusable specification library
  CImporter/                -- Python: clang JSON -> .lean
  Generated/                -- Output of CImporter (version controlled)
  Examples/                 -- User proofs and worked examples
  test/                     -- C sources, expected outputs, tests
  tools/                    -- VS Code extension, CI integration
  docs/                     -- This user guide, ADRs
  Justfile                  -- Common commands
  lakefile.lean             -- Lake build configuration
```


## Measuring Verification Progress

Use `just status` or `just sorry-count` to check progress.

Key metrics:
- **Functions imported**: count `*_body` definitions in `Generated/`
- **Functions lifted**: count `l1_*_body` definitions
- **L1corres proofs**: count `l1_*_body_corres` theorems
- **FuncSpecs**: count `FuncSpec` definitions in `Examples/`
- **Sorry count**: must be 0 for verified code
- **Axiom audit**: `#print axioms theorem_name` shows dependencies
