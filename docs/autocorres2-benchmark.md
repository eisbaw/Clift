# AutoCorres2 Benchmark: Clift vs AutoCorres2 on the Same C File

## Benchmark File: `factorial.c`

Selected from `ext/AutoCorres2/tests/examples/factorial.c` (Data61/CSIRO, BSD-2).

```c
unsigned factorial(unsigned n) {
    if (n == 0) { return 1; }
    return n * factorial(n - 1);
}

unsigned call_factorial(void) {
    return factorial(42);
}
```

This file is a good benchmark because:
- It has recursion (tests termination handling)
- It has arithmetic (tests word-level reasoning)
- It has a clear spec (factorial function)
- AutoCorres2 has a complete proof (`FactorialTest.thy`)
- It is small enough to compare line-by-line

**Limitation**: Clift does not currently handle recursive function calls
(CSimpl has no `.call` constructor for self-recursion). This means we can
only compare the import/lifting pipeline, not the full proof. The comparison
is still valuable for measuring infrastructure maturity.

## Comparison: Import Pipeline

### AutoCorres2 (Isabelle/HOL)

```isabelle
-- Install C file into Isabelle
install_C_file "factorial.c"

-- AutoCorres lifts through 3 stages automatically:
-- 1. L1: local variable extraction
-- 2. L2: monad simplification
-- 3. TS: type strengthening (word -> nat)
autocorres [ts_rules=nondet] "factorial.c"
```

**Import time**: Seconds (C parser is compiled Haskell, integrated into Isabelle).
**Lifting**: Fully automatic through L1/L2/TS stages.
**Output**: Isabelle `factorial'` definition in a monadic form.

### Clift (CImporter + Lean 4)

```bash
# Step 1: clang AST dump
clang -Xclang -ast-dump=json -fsyntax-only factorial.c > factorial.json

# Step 2: CImporter translates to CSimpl
python3 CImporter/import.py factorial.json -o Generated/Factorial.lean
```

**Import time**: Sub-second (clang JSON dump + Python string processing).
**Lifting**: Manual L1 monadic form (MetaM automation in progress).
**Output**: Lean 4 `factorial_body : CSimpl ProgramState` definition.

## Comparison: Generated Definitions

### AutoCorres2 Output (Isabelle)

AutoCorres2 produces a monadic function after full lifting:

```isabelle
factorial' :: "32 word => (unit, 32 word) nondet_monad"
factorial' n = do {
  if n = 0 then return 1
  else do {
    r <- factorial' (n - 1);
    return (n * r)
  }
}
```

Key properties:
- Recursion is preserved as Isabelle function recursion
- Types are `32 word` (machine words)
- Monad is `nondet_monad` (nondeterminism for UB)
- Automatic termination proof via `word_induct2`

### Clift Output (Lean 4)

CImporter produces a CSimpl term (not yet lifted):

```lean
def factorial_body : CSimpl ProgramState :=
  .catch
    (.seq
      (.cond (fun s => decide (s.locals.n = 0))
        (.seq (.basic (fun s => { s with locals := { s.locals with ret__val := 1 } }))
              .throw)
        .skip)
      (.seq
        -- NOTE: recursive call would need .call constructor
        (.basic (fun s => { s with locals := { s.locals with ret__val := ... } }))
        .throw))
    .skip
```

Key properties:
- No recursion support yet (CSimpl lacks `.call` for self-recursion)
- Types are `UInt32` (Lean native, maps to `Fin (2^32)`)
- Monad is `NondetM` via L1 lifting (manual step today)
- No automatic termination

## Detailed Comparison

### Where Clift is Simpler

| Aspect | AutoCorres2 | Clift | Advantage |
|--------|-------------|-------|-----------|
| C parser | Custom Haskell StrictC parser (~10K LOC) | clang JSON AST + Python (~2K LOC) | Clift: smaller TCB, leverages industrial parser |
| Build system | Complex Isabelle session + C parser build | Nix flake + `lake build` | Clift: standard tooling, reproducible |
| Type system | Isabelle/HOL (simple types + type classes) | Lean 4 (dependent types) | Clift: more expressive types for specs |
| Proof language | Isar + tactics | Lean 4 tactics | Clift: unified language for specs and proofs |
| Setup | Isabelle + AFP + AutoCorres2 (~2GB) | Lean 4 + Mathlib cache (~1GB) | Comparable, slight edge to Clift |

### Where AutoCorres2 is More Mature

| Aspect | AutoCorres2 | Clift | Advantage |
|--------|-------------|-------|-----------|
| Lifting automation | Fully automatic (L1/L2/TS) | Manual L1, no L2/TS yet | AutoCorres2: decades of engineering |
| Recursion | Full support with termination | No `.call` constructor | AutoCorres2: fundamental capability |
| Function calls | Full inter-procedural | Single-function only | AutoCorres2: real programs |
| Heap reasoning | Separation logic (UMM) | Basic typed heap (HeapRawState) | AutoCorres2: more mature |
| Word arithmetic | `word_induct`, `unat_arith` | Lean `omega`, `UInt32.toNat` | AutoCorres2: richer word library |
| Track record | seL4 kernel verified (10K LOC) | ~1K LOC verified | AutoCorres2: proven at scale |
| Proof automation | `runs_to_vcg`, `wpsimp` | `l1_vcg_finish`, basic VCG | AutoCorres2: stronger automation |
| Community | Active Isabelle AFP community | Growing Lean4 community | AutoCorres2: more verification users |

### Where Clift Has Potential Advantages

| Aspect | Why |
|--------|-----|
| TCB minimality | clang is a more trustworthy C parser than a custom Haskell parser |
| Modern language | Lean 4 has better IDE support, faster compilation, active development |
| Composability | Lean 4 package manager (lake) vs Isabelle sessions |
| AI integration | Lean 4 has growing LLM proof generation tooling |
| Dependent types | Can express richer specifications than simple type theory |

## Proof Effort Comparison

### AutoCorres2: `FactorialTest.thy`

```
Lines of proof (excluding comments/imports): ~35
Key tactics: runs_to_vcg, word_induct2, simp, auto
Automation level: HIGH (runs_to_vcg closes most VCs automatically)
Termination: automatic via word_induct2
```

### Clift: Not Yet Possible

Clift cannot verify factorial because:
1. No recursive call support in CSimpl
2. No termination framework
3. No word induction tactics

**Estimated effort when infrastructure exists**: ~30-50 lines
(comparable to AutoCorres2, once L1/L2 lifting and VCG are automated).

## Conclusions

1. **AutoCorres2 is significantly more mature** for end-to-end C verification.
   It has 15+ years of engineering behind it and has verified a real OS kernel.

2. **Clift's architecture is sound** but needs more engineering:
   - Recursive function support (CSimpl `.call`)
   - Automatic L1/L2 lifting (MetaM tactics)
   - Stronger VCG automation

3. **Clift's TCB may be smaller** because it relies on clang (industrial,
   heavily tested) rather than a custom C parser. This is a genuine
   advantage for certification arguments.

4. **The Lean 4 platform offers long-term advantages** in tooling,
   AI integration, and language expressiveness. Whether these translate
   to practical verification advantages remains to be demonstrated.

5. **Near-term recommendation**: Focus on the gaps identified above
   (recursion, lifting, automation) before claiming parity with AutoCorres2.
   The swap and GCD proofs demonstrate the architecture works; factorial
   would demonstrate it scales to recursion.
