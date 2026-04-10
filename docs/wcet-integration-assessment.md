# WCET Integration Assessment

## Purpose

Document how Clift's formal proofs could integrate with Worst-Case Execution Time (WCET) analysis tools for safety-critical certification (DO-178C for aerospace, ISO 26262 for automotive, IEC 62304 for medical devices).

## Background

### What is WCET analysis?
WCET analysis determines an upper bound on the execution time of a program. Safety-critical standards require demonstrable timing bounds:
- **DO-178C (DAL-A)**: All code must have bounded execution time; unbounded loops are forbidden
- **ISO 26262 (ASIL-D)**: Real-time constraints must be verified; timing failures are safety violations
- **IEC 62304 (Class C)**: Timing requirements must be specified and verified

### How seL4 handled WCET
seL4 provided sound WCET bounds for all system calls:
1. All loops in the kernel have proven bounds
2. The binary was analyzed with a WCET tool (Chronos initially, later custom analysis)
3. Loop bounds from the formal proofs were provided to the WCET tool as annotations
4. The combination of verified loop bounds + binary-level timing analysis gives sound WCET

## Clift's Relevant Capabilities

### What Clift can provide today
1. **Termination proofs**: The `Terminates` predicate (CSemantics/Terminates.lean) proves that loops terminate with specific ranking functions
2. **Loop invariants**: Every verified while loop has an invariant that constrains iteration counts
3. **Function call depth**: The call graph analysis shows maximum recursion depth
4. **Absence of undefined behavior**: Guard conditions in CSimpl ensure no UB occurs, which is a prerequisite for meaningful WCET analysis (UB makes timing analysis meaningless)

### What Clift cannot provide
1. **Hardware-specific timing**: Clift operates at the source/semantic level, not the instruction/cycle level. Pipeline effects, cache behavior, and branch prediction are out of scope.
2. **Compiler optimization effects**: Clift verifies the C source semantics, not the compiled binary. Compiler optimizations can change timing characteristics.
3. **Interrupt latency**: Interrupt handling timing depends on hardware and is not modeled in CSimpl's semantics.

## Integration Architecture

### Overview
```
Clift (Lean 4)                    WCET Tool (aiT, Chronos, OTAWA)
     |                                   |
     |  1. Extract loop bounds           |
     |     from termination proofs       |
     |                                   |
     v                                   v
  Loop Bound                       Binary Analysis
  Annotations                     (instruction timing)
  (per-function)                        |
     |                                   |
     +-----------> Combined <------------+
                   WCET Bound
                   (sound, tight)
```

### Step 1: Loop Bound Extraction

Clift's termination proofs use well-founded recursion with ranking functions. The ranking function provides a bound on the number of iterations:

```
-- Clift termination proof shape:
-- "while (b != 0) { t = b; b = a % b; a = t; }"
-- Ranking function: b (decreases on each iteration because a % b < b)
-- Bound: initial value of b
```

To extract this for WCET tools, we need a function:
```
extractLoopBound : TerminationProof -> (functionName, loopId, boundExpr)
```

The bound expression would be in terms of function parameters (e.g., "loop at line 5 iterates at most `b` times where `b` is the second parameter").

### Step 2: Annotation Format

WCET tools accept loop bounds as annotations. Common formats:

**aiT (AbsInt)**:
```
routine "gcd" {
  loop 0x1234 max 32;  -- address of loop header, max iterations
}
```

**OTAWA**:
```xml
<loop address="0x1234" maxcount="32" />
```

**Clift export format** (proposed):
```json
{
  "function": "gcd",
  "loops": [
    {
      "source_line": 5,
      "bound_expr": "param_b",
      "bound_type": "dynamic",
      "static_max": null,
      "ranking_function": "b",
      "proof_ref": "gcd_terminates"
    }
  ]
}
```

### Step 3: Dynamic to Static Bounds

WCET tools often need static (numeric) bounds, not symbolic ones. Two approaches:

1. **User provides parameter bounds**: "gcd is called with a,b in [0, 2^32). So loop bound is 2^32." This is sound but loose.

2. **Context-sensitive bounds**: At each call site, the caller's precondition constrains the arguments. Clift could extract these constraints from the Hoare triple preconditions.

3. **Interaction with ISO 26262**: ASIL-D requires that timing budgets are allocated per function. The user specifies the budget; Clift's loop bounds + WCET tool verifies it is met.

## Certification Context

### DO-178C Objective Coverage

| DO-178C Objective | Clift Contribution |
|---|---|
| OBJ 6.3.1: Source code accuracy | CImporter fidelity (TCB analysis in docs/tcb.md) |
| OBJ 6.3.2: Source code conformance to standards | CSimpl enforces C subset restrictions |
| OBJ 6.3.3: Source code is traceable | Refinement chain from C to abstract spec |
| OBJ 6.3.4: Source code is verifiable | Formal proofs as verification evidence |
| OBJ 6.4.1: Executable object code is robust | Out of scope (binary level) |

### ISO 26262 Part 6 Method Coverage

| ISO 26262 Method | ASIL D | Clift Contribution |
|---|---|---|
| 1a: Walk-through of design | ++ | Abstract spec review |
| 1b: Inspection of design | ++ | Formal spec as design document |
| 1c: Semi-formal verification | ++ | Refinement proofs |
| 1d: Formal verification | ++ | Machine-checked proofs |
| 1e: Control flow analysis | ++ | CSimpl execution analysis |
| 1f: Data flow analysis | + | Partial (state tracking) |

## Gaps and Limitations

1. **No binary-level integration yet**: Clift proofs are about source-level semantics. Connecting to binary requires either a verified compiler (CompCert) or binary verification (task-0128).

2. **Compiler trust gap**: If the compiler optimizes a bounded loop into something with different timing, the source-level bound does not apply. Mitigation: use CompCert or restrict optimizations.

3. **Interrupt timing**: CSimpl does not model interrupt latency. For interrupt-driven systems, the WCET analysis must account for interrupt overhead separately.

4. **Cache and pipeline effects**: Entirely out of scope for Clift. The WCET tool handles these at the binary level.

5. **Loop bound tightness**: Termination proofs give VALID bounds but not necessarily TIGHT bounds. A ranking function of `b` for GCD gives an O(b) bound when O(log(b)) is achievable. Tighter bounds require more sophisticated ranking functions.

## Recommendations

1. **Short term**: Document loop bound extraction format and provide manual examples
2. **Medium term**: Implement a Lean 4 metaprogram that extracts loop bounds from termination proofs and writes them in WCET tool annotation format
3. **Long term**: Integrate with a specific WCET tool (aiT is the industry standard for DO-178C) and demonstrate end-to-end certified timing analysis on a real embedded function
4. **For ISO 26262**: Partner with an automotive tool vendor who already does WCET analysis and provide Clift as the formal verification component of their toolchain
