# External References

Papers, theses, and source code relevant to Clift.

## Source Code (primary reference)

| Path | What | Why it matters |
|------|------|----------------|
| AutoCorres2/ | AFP entry: AutoCorres2 (Isabelle/HOL), Feb 2025 | **The source we are porting to Lean 4.** 57K lines. Complete lifting pipeline, C parser, memory model, tests. By Greenaway, Klein, Schirmer, Sewell, Tuch et al. From https://www.isa-afp.org/entries/AutoCorres2.html |
| AutoCorres2/SimplConv.thy + simpl_conv.ML | L1: CSimpl -> monadic form | Our Clift/Lifting/SimplConv.lean |
| AutoCorres2/LocalVarExtract.thy + local_var_extract.ML | L2: locals extraction | Our Clift/Lifting/LocalVarExtract.lean |
| AutoCorres2/TypeStrengthen.thy + type_strengthen.ML | L3: monad narrowing (pure/gets/option/nondet) | Our Clift/Lifting/TypeStrengthen.lean |
| AutoCorres2/HeapLift.thy + heap_lift.ML | L4: typed heap abstraction | Our Clift/Lifting/HeapLift.lean |
| AutoCorres2/WordAbstract.thy + word_abstract.ML | L5: BitVec -> Int/Nat | Our Clift/Lifting/WordAbstract.lean |
| AutoCorres2/CorresXF.thy | Correspondence (refinement) definitions | Our Clift/MonadLib/Corres.lean |
| AutoCorres2/L1Defs.thy, L2Defs.thy | Monad definitions per stage | Our Clift/MonadLib/NondetM.lean |
| AutoCorres2/TypHeapSimple.thy | Simplified split heap model | Our Clift/Lifting/HeapLift/SimpleLift.lean |
| AutoCorres2/Split_Heap.thy | Split heap predicates | Our Clift/Lifting/HeapLift/SplitHeap.lean |
| AutoCorres2/monad_types.ML | Monad type registry (pure/gets/option/nondet) | Our Clift/Lifting/TypeStrengthen.lean |
| AutoCorres2/c-parser/ | StrictC parser (SML) | Reference for our CImporter (Python) |
| AutoCorres2/tests/ | 300+ test cases | Test targets for our pipeline |

## Papers

| File | What | Why it matters |
|------|------|----------------|
| autocorres-pldi2014.pdf | Greenaway et al. PLDI 2014 "Don't Sweat the Small Stuff" | AutoCorres lifting pipeline — condensed overview |
| simpl-schirmer.pdf | Schirmer 2006 PhD thesis, Simpl framework (246pp) | The Simpl language our CSimpl is based on |
| sel4-sosp2009.pdf | Klein et al. SOSP 2009 "seL4: Formal Verification of an OS Kernel" | Original seL4 verification paper — methodology and cost model |
| sel4-comprehensive-tocs2014.pdf | Klein, Andronick et al. TOCS 2014 "Comprehensive Formal Verification" | Extended seL4 — binary verification, IPC fastpath, security proofs |
| tuch-types-bytes-seplogic-popl2007.pdf | Tuch, Klein, Norrish POPL 2007 "Types, Bytes, and Separation Logic" | Memory model combining C byte semantics with separation logic |

## To find manually

| File | What | Why it matters |
|------|------|----------------|
| seL4-autocorres-thesis.pdf | Greenaway 2015 PhD thesis (full AutoCorres details) | Superseded by AutoCorres2/ source for implementation details |

## To create as we go

| File | What | Why it matters |
|------|------|----------------|
| lean4-metaprogramming.md | Collected notes on Lean 4 MetaM/TacticM patterns | Implementation reference for lifting stages |
| aeneas-progress-tactic.md | Notes on Aeneas's progress/step tactic design | Template for our c_step tactic |
