# Clift: Lifting C into Lean 4 for Formal Verification

Clift verifies imperative C code with the same rigor as [seL4](https://sel4.systems/), but using [Lean 4](https://lean-lang.org/) instead of Isabelle/HOL. It replicates the [AutoCorres](https://trustworthy.systems/projects/OLD/autocorres/) pipeline — parsing C, embedding it formally, lifting through abstraction stages, and proving properties that chain back to the actual C.

The key idea: we verify the C that actually runs, not a rewrite or model of it.

## Methodology

Clift follows seL4's AutoCorres approach: **backward simulation** (refinement) through a sequence of abstraction stages. Each stage produces a transformed function definition and a machine-checked `corres` lemma proving the transformation preserves all behaviors.

```
C source (.c)
    |  clang -ast-dump=json
    v
[Stage 0: CImporter]       Python script, reads JSON AST, emits .lean files
    |  CSimpl terms (deeply embedded imperative language)
    v
[Stage 1: SimplConv]        Lean 4 metaprogram + corres proof
    |  Shallow monadic embedding (nondeterministic state monad + failure)
    v
[Stage 2: LocalVarExtract]  Lean 4 metaprogram + corres proof
    |  Locals become lambda-bound Lean variables
    v
[Stage 3: TypeStrengthen]   Lean 4 metaprogram + corres proof
    |  Tightest monad per function (pure/option/nondet)
    v
[Stage 4: HeapLift]         Lean 4 metaprogram + corres proof
    |  Flat bytes -> typed split heaps (simplified Burstall-Bornat)
    v
[Stage 5: WordAbstract]     Lean 4 metaprogram + corres proof
    |  BitVec n -> Int/Nat with range guards
    v
[User writes specs + proofs about clean functional model]
    |  Correctness chains back to C via composed corres lemmas
    v
Verified C
```

The Lean 4 kernel is the sole trust anchor. Every lifting proof, Hoare triple, and correspondence lemma is kernel-checked. Tactics, metaprograms, and AI-generated proofs are all untrusted oracles whose output the kernel verifies.

For full architectural details, design decisions, and rationale, see [plan.md](plan.md).

## Current State

**Phases 0-4 complete.** The core pipeline works end-to-end: C source goes through all lifting stages with machine-checked refinement proofs at each step.

What works:
- **CImporter**: integers (signed/unsigned), pointers, structs (with padding/alignment), arrays, enums, typedefs, globals, function calls, for/do-while/switch, signed overflow UB guards, division-by-zero guards, uninitialized local detection, multi-function files
- **All 5 lifting stages automated** via Lean 4 MetaM metaprograms
- **Unified `clift` command** for one-shot full pipeline
- **Tactics**: VCG (verification condition generation), c_step, sep_auto (separation logic with frame reasoning), corres_auto
- **Function specification framework** with pre/postconditions and modifies-set inference
- **Weakest precondition calculus** for L1 monadic programs
- **AI-assisted proof**: loop invariant generation, data structure invariant generation, specification drafting from C signatures
- **24+ C programs** imported and verified to varying degrees, including ring buffers, hash tables, packet parsers, UART drivers, red-black trees, priority queues, and a 676-LOC seL4-scale test

## Limitations

- **No floating point** support
- **No goto, longjmp, switch fall-through, VLAs, variadic functions**
- **No address-of local variables** (locals are value-typed, not heap-allocated)
- **No bitwise operations** in CImporter yet (task 0119)
- **No type casts or sizeof** in CImporter yet (task 0120)
- **No multi-file compilation units** (task 0122)
- **No union types or void pointers** (task 0123)
- **CImporter is in the TCB** — if it mistranslates C to CSimpl, proofs are about the wrong program. Mitigated by regression tests, snapshot testing, and differential testing against gcc
- **Clang JSON AST is not formally versioned** — pinned to a specific LLVM version via nix flake
- **Struct field sub-pointers not supported** in lifted heap — structs are accessed as whole values (same restriction as AutoCorres)
- **Proof effort** is still significant for complex properties, though AI assistance and automation are reducing it

See [docs/tcb.md](docs/tcb.md) for the full trusted computing base analysis and [docs/c11-coverage.md](docs/c11-coverage.md) for C11 standard coverage.

## Installation

### Prerequisites

- [Nix](https://nixos.org/download.html) with flakes enabled

### Setup

```bash
git clone https://github.com/eisbaw/Clift.git
cd Clift

# Enter development shell (provides Lean, clang, Python, just, etc.)
nix develop

# Fetch Mathlib cache (run once — saves 30-60 min vs building from source)
just setup

# Build everything
just build
```

### Quick Start

Import a C file and build:

```bash
# Import a C file (generates Lean CSimpl definitions)
just import test/c_sources/gcd.c Gcd

# Build all Lean code
just build
```

Run tests:

```bash
# Full end-to-end test suite
just e2e

# Individual test suites
just test-importer      # CImporter Python unit tests
just test-snapshots     # Generated code matches expected output
just test-struct-layout # Struct padding/alignment matches gcc
just test-fuzz          # Fuzz CImporter with random C programs
```

See [docs/user-guide.md](docs/user-guide.md) for a walkthrough of verifying a C function.

### Key Commands

| Command | Description |
|---|---|
| `just build` | Build all Lean code (library + generated + examples) |
| `just build-lib` | Build only core Clift library |
| `just import FILE NAME` | Import a C file via CImporter |
| `just import-all` | Re-import all known C sources |
| `just e2e` | Full end-to-end test suite |
| `just ci` | CI pipeline (sorry check + tests + build) |
| `just sorry-count` | Count remaining sorry statements |
| `just prove FILE` | Run AI proof engine on a file |
| `just status` | Show project status |

## Project Structure

```
Clift/                  Core Lean 4 library
  MonadLib/               Nondeterministic monad, Hoare triples, corres
  CSemantics/             CSimpl language, big-step Exec, state, memory model
  Lifting/                L1-L5 transformation stages + automation
  Tactics/                VCG, c_step, sep_auto, corres_auto
  AI/                     Invariant/spec generation, proof indexing
  Security/               Integrity, confidentiality, access control
  Specs/                  Reusable specification templates
CImporter/              Python: clang JSON AST -> Lean CSimpl definitions
  proof_engine/           AI-assisted sorry elimination
Generated/              Auto-generated CSimpl code (24+ C programs)
Examples/               Correctness proofs and lifting demonstrations
test/                   C sources, snapshots, fuzz testing, audits
docs/                   User guide, TCB analysis, C11 coverage, ADRs
ext/                    Reference papers + AutoCorres2 Isabelle source
```

## Related Work

Clift is a Lean 4 port of the ideas in seL4's [AutoCorres2](https://www.isa-afp.org/entries/AutoCorres2.html) (Isabelle/HOL). No code is copied verbatim — the type systems, proof styles, and metaprogramming APIs are completely different — but every Lean module has a `-- Reference:` comment tracing its lineage to the corresponding Isabelle theory.

**Direct lineage:**
- [AutoCorres2](https://www.isa-afp.org/entries/AutoCorres2.html) — the Isabelle/HOL pipeline we are porting (Greenaway, Lim, Klein, Holzl, Immler, Schirmer, Sickert-Zehnter, Wimmer)
- [Simpl](https://isa-afp.org/entries/Simpl.html) — Schirmer's imperative language framework (our CSimpl is modeled on this)
- [seL4](https://sel4.systems/) — the verified OS kernel whose methodology we follow (Klein et al., SOSP 2009; TOCS 2014)

**Key papers:**
- Greenaway et al., "Don't Sweat the Small Stuff" (PLDI 2014) — AutoCorres pipeline design
- Schirmer, "Verification of Sequential Imperative Programs in Isabelle/HOL" (PhD thesis, 2006) — Simpl framework
- Tuch, Klein, Norrish, "Types, Bytes, and Separation Logic" (POPL 2007) — memory model and separation logic
- Klein et al., "Comprehensive Formal Verification of an OS Microkernel" (TOCS 2014) — seL4 methodology

**Other verification tools for C:**
- [CompCert](https://compcert.org/) — verified C compiler (Coq), complementary: CompCert proves the compiler correct, Clift proves programs correct
- [VST](https://vst.cs.princeton.edu/) — Verified Software Toolchain (Coq), program logic for CompCert C
- [Frama-C](https://frama-c.com/) — C analysis platform with WP plugin (SMT-based, not proof-assistant-based)
- [Aeneas](https://github.com/AeneasVerif/aeneas) — Rust verification via Lean 4 (similar spirit, different source language)

**Why Lean 4 instead of Isabelle:**
- Access to Lean's AI ecosystem (grind, LLM proof search, Mathlib)
- Lean 4 compiles to native code — faster kernel checking for large proofs
- MetaM metaprogramming for tactic and automation development
- Growing community and tooling

## Goals

**Near-term:** Complete CImporter coverage for industrial C (bitwise ops, casts, multi-file), verify a real-world embedded C module (RTOS scheduler, crypto primitive, or device driver) with full functional correctness.

**Long-term:** Reach seL4-level assurance for C code verified in Lean 4 — functional correctness, security properties (integrity, confidentiality, noninterference), and a verified refinement chain from abstract specification down to C source.

See the [backlog](backlog/) for the full task list and [plan.md](plan.md) for the phased roadmap.

## License

BSD. See [LICENSE](LICENSE) (pending).

Attribution for the AutoCorres2 reference material under `ext/` is documented in [ext/AutoCorres2/README.md](ext/AutoCorres2/README.md).
