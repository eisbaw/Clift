---
id: doc-0001
title: 'Sebastian Graf feedback: Std.Do.Triple, mvcgen, skip CSimpl'
type: note
created_date: '2026-04-14 21:21'
---

# Sebastian Graf Feedback (2026-04-14)

Sebastian Graf (Lean FRO) commented on Clift with suggestions.

## Comments to us

> If this all checks out, this would be a great addition to the Lean ecosystem! See also
> #Program verification > AutoCorres in Lean where I made a far less ambitious PoC to test
> whether mvcgen could be used for VC generation. It can, so I would suggest you use
> Std.Do.Triple to express validHoare instead and use mvcgen to prove lemmas such as
> auto_l1_gcd_body_validHoare. That would get rid of stuff like simp only [L1.seq] and it
> might also help with the kernel reduction issue.
>
> Any reason why you kept targeting CSimpl from CImporter? I just had a call today with
> industry users and got some feedback on their use of AutoCorres2 to verify crypto
> applications and they considered the existence of CSimpl a legacy artifact. You could
> define a denotational semantics on some representation of the C AST that maps into the
> SpecM monad (that you don't seem to define explicitly, only NondetM)? I guess that amounts
> to moving the L1 translation into CImporter and absorbing L1corres proofs into the trusted
> code base. That doesn't seem too bad to me compared to the reduction in complexity.

## Earlier Zulip post (general, not to us)

> AutoCorres2 is an Isabelle framework for verifying C code. Roughly, if Aeneas goes from
> Rust to Lean, then AutoCorres2 goes from C to Isabelle. It has been used to verify the
> seL4 microkernel in the past (v1, anyway) and is used by big players in industry.
> Furthermore, the bulk of it can be recast as a (partially evaluated) denotational
> semantics from C AST into a certain SpecM monad if you simply skip the SIMPL IR (I don't
> see a reason to keep it).
> Reason enough for me to see how we could port it to Lean and use mvcgen to reason about
> SpecM programs. You can find the result of a couple of days of vibe coding at
> https://github.com/sgraf812/LeanCorres.
> I'd say that mvcgen works for this use case, but of course much more work needs to be done
> to turn this PoC into a proper tool. OTOH
>
> One would need to write the proper C to Clight AST frontend
> There needs to be what AutoCorres2 calls the "unified memory model"; a heap typing
> discipline maintained in a separation logic. (Aside: mvcgen will get support for VC
> generation into separation logics in Q2, but it's not there yet.)
> Anyway, wanted to post these findings before they bitrot in my repo. This might be
> interesting to pursue for industry players.

---

## LeanCorres PoC Analysis

**Repo**: https://github.com/sgraf812/LeanCorres (8 commits, ~2K LOC, 2026-03-25)

### Architecture

LeanCorres skips CSimpl/SIMPL entirely. It defines:

1. **SpecM monad** (`AutoCorres2.lean`): `σ → PostState (Outcome ε α × σ)` where PostState
   is either `failure` (UB/nontermination) or `success (α → Prop)` (set of outcomes,
   demonic nondeterminism). This is a faithful port of AutoCorres2's Spec_Monad.

2. **Clight AST** (`CLight.lean`): Lean inductives for types, expressions, statements.
   `denoteStmt` maps Clight statements directly into SpecM. No intermediate IR.

3. **Examples** (`Examples.lean`): swap, cube root (while loop), and a full Schorr-Waite
   proof (~800 lines) demonstrating mvcgen on complex pointer algorithms.

### How mvcgen is used

- `@[spec]` lemmas tagged for all SpecM primitives (getState, setState, modify, throwE, whileLoop)
- Simple proofs: `mvcgen [incrState] with grind` — fully automatic
- Complex proofs: `mvcgen [schorrWaite] invariants · WhileInvariant.mk' ...` with manual
  invariant supply

### What works

- SpecM monad with CCPO structure, LawfulMonad, WP/WPMonad instances: complete and proven
- whileLoop via CCPO least fixpoint with WhileInvariant (includes Acc R for termination): proven
- Schorr-Waite (~800 lines, sorry-free): demonstrates the approach handles hard algorithms

### What doesn't work yet (4 sorry)

- `callFun_spec` — function call spec through SpecM
- `denoteStmt_call_spec` — statement-level call spec
- `swap_clight_correct` — end-to-end CLight-to-SpecM verification
- `double_satisfies` — function spec satisfaction

The sorries are concentrated in the **CLight-to-SpecM bridge**, exactly where CSimpl/L1corres
would normally provide proven correctness. This suggests skipping CSimpl trades one kind of
complexity (corres proofs) for another (denotational semantics correctness).

### What's missing entirely

- C parser (everything is hand-embedded Lean)
- Memory model / unified heap typing
- Separation logic (planned for mvcgen Q2 2026)
- Most unary ops, division, bitwise, shifts
- Struct field access, arrays

---

## Comparison: Clift vs LeanCorres

| Aspect | Clift | LeanCorres |
|--------|-------|-----------|
| Pipeline stages | 5 (CSimpl→L1→L2→L3→L5) | 1 (Clight→SpecM) |
| C parser | Clang JSON → Python CImporter | None (manual) |
| Monad | NondetM (custom) | SpecM (AC2-faithful port) |
| Hoare logic | Custom validHoare + L1HoareRules | Std.Do.Triple + mvcgen |
| While loops | Custom loop rules | whileLoop via CCPO lfp |
| TCB | CImporter only (corres is proven) | CImporter + denotation (larger) |
| Maturity | ~55K LOC, 260 tasks, real C | ~2K LOC, 8 commits, manual examples |

---

## Suggestion 1: Use Std.Do.Triple + mvcgen instead of custom validHoare

- Would replace: custom validHoare (~60 LOC), L1HoareRules (~960 LOC), Tactics/ (~675 LOC)
- Would eliminate the painful `simp only [L1.seq]` chains
- May help with kernel reduction issues

### Limitations (as of 2026-04-14)

- **While loops**: LeanCorres defines its own whileLoop with WhileInvariant + WP instance,
  so this works. But mvcgen's native while support is Q2 2026.
- **SpecM is not in stdlib** — it's defined in LeanCorres. Would need to be adopted or
  ported into Clift.
- **Separation logic support in mvcgen**: Q2 2026.

## Suggestion 2: Skip CSimpl, emit monadic code directly from CImporter

- Industry AutoCorres2 users consider CSimpl a "legacy artifact"
- Would eliminate: CSimpl (~64 LOC), Exec (~239 LOC), L1corres proofs, SimplConv (~604 LOC)
- TCB tradeoff: CImporter absorbs L1corres responsibility
- LeanCorres validates this approach but its sorries at the CLight bridge show the
  denotational semantics correctness is not free

## Open Questions

1. Can we adopt SpecM (from LeanCorres) as our monad, replacing NondetM?
2. Can CImporter emit do-notation SpecM code that mvcgen can process?
3. LeanCorres's sorries at the CLight bridge — would we hit the same gap?
4. Separation logic support in mvcgen (Q2 2026) — can we wait, or do we need it now?
5. Paper: describe current architecture or the pivot? Future work?
6. Could we collaborate with Sebastian on a shared SpecM / LeanCorres foundation?

## References

- https://github.com/sgraf812/LeanCorres — Sebastian's PoC
- Zulip: #Program verification > AutoCorres in Lean
- Lean reference manual: The mvcgen tactic
- Lean stdlib: Std.Do.Triple, Std.Do.WP
