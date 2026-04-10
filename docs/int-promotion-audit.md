# Integer Promotion Audit

Task 0141: Audit of every BinaryOperator emission in lean_emitter.py.

## Audit Scope

File: `CImporter/lean_emitter.py`, method `_emit_expr`, case `expr.kind == "binop"`.

## BinaryOperator Mapping (lines ~894-909)

```python
lean_op = {
    "+": "+", "-": "-", "*": "*", "/": "/", "%": "%",
    "&": "&&&", "|": "|||", "^": "^^^",
    "<<": "<<<", ">>": ">>>",
    "&&": "&&", "||": "||",
}.get(op, op)
```

### Arithmetic Operators (+, -, *, /, %)

**C11 behavior**: Operands undergo "usual arithmetic conversions" (6.3.1.8):
1. Integer promotion: types narrower than `int` promote to `int`
2. If both operands have the same type after promotion, use that type
3. Otherwise, convert the narrower type to the wider type
4. Signed/unsigned mismatch: complex rules (see C11 6.3.1.8p1)

**Our model**: We emit the operator directly on the Lean types corresponding
to the C declared types. We rely on clang's AST to include `ImplicitCastExpr`
nodes for promotions.

**Finding**: This is CORRECT because:
- Clang's AST already includes ImplicitCastExpr for integer promotions
- The CImporter handles `cast_expr` nodes (lines ~954-974)
- So by the time we see a BinaryOperator, both operands are already at the
  promoted type (clang has inserted the casts)

**Risk**: If a future change bypasses clang's type system, promotions would
be missed. This is a TCB risk.

### Comparison Operators (<, >, <=, >=, ==, !=)

**C11 behavior**: Same promotion rules as arithmetic, but result is `int`
(0 or 1).

**Our model**: Emits `(if lhs op rhs then 1 else 0)`, producing a UInt value.
The promotions come from clang's ImplicitCastExpr.

**Finding**: CORRECT. The `if/then/else` pattern correctly models C's
integer-valued comparisons.

### Bitwise Operators (&, |, ^)

**C11 behavior**: Integer promotion applies. Result type is the promoted type.

**Our model**: Maps to Lean's `&&&`, `|||`, `^^^`. Works correctly on UInt types.

**Finding**: CORRECT for same-width operands. Cross-width promotion handled
by clang's ImplicitCastExpr.

### Shift Operators (<<, >>)

**C11 behavior**: Left operand undergoes integer promotion. Result type is
the promoted type of the left operand. The right operand is independently
promoted. UB if right operand is negative or >= width of promoted left type.

**Our model**: Maps to `<<<`, `>>>`. No guard for shift-by-width UB.

**Finding**: LIMITATION. Missing guard for:
- Shift count >= bit width of type (UB in C, wraps in Lean)
- Negative shift count (UB in C, not applicable for unsigned in Lean)

### Logical Operators (&&, ||)

**C11 behavior**: Short-circuit evaluation. Operands promoted to int.
Result is int (0 or 1).

**Our model**: In `_emit_expr`, maps to `&&`, `||`. In `_emit_bool_expr`,
generates proper Bool expressions. No short-circuit modeling.

**Finding**: CORRECT under StrictC. StrictC prohibits side effects in
expressions, so short-circuit evaluation is only observable for UB-triggering
sub-expressions (which we guard against separately).

## Edge Case Analysis

### Case 1: uint8_t + uint8_t (AC #2)

```c
uint8_t a = 200, b = 200;
uint32_t c = a + b;  // C: promotes to int, computes 400
```

Clang AST includes: `ImplicitCastExpr 'int' <IntegralCast>` on both operands.
CImporter sees: `BinaryOperator 'int' '+'` with promoted operands.
Result: correct (400).

### Case 2: int8_t + uint8_t (AC #3)

```c
int8_t a = -1; uint8_t b = 200;
int32_t c = a + b;  // C: both promote to int, -1 + 200 = 199
```

Clang AST: ImplicitCastExpr to int on both. CImporter handles correctly.

### Case 3: uint16_t * uint16_t overflow (AC #4)

```c
uint16_t a = 60000, b = 60000;
uint32_t c = (uint32_t)a * (uint32_t)b;  // Explicit cast avoids UB
```

Without explicit cast: both promote to int (signed 32-bit). 60000*60000 =
3,600,000,000 which overflows int32 (max 2,147,483,647). This is UB.

With explicit cast (as written): both are uint32_t, unsigned multiplication
wraps modulo 2^32. Result: 3,600,000,000 (fits in uint32_t). No UB.

Our model: If the programmer writes the explicit cast, clang AST reflects it,
and CImporter emits the cast. Without the cast, clang AST has the promotion
to int, and our signed overflow guard catches the overflow.

**Finding**: CORRECT. The guard catches the implicit promotion overflow case.

## Summary of Findings

| Operator | Promotion | Our Treatment | Status |
|----------|-----------|---------------|--------|
| +, -, * | Integer promotion via clang | Relies on ImplicitCastExpr | CORRECT |
| /, % | Same + div-by-zero guard | Guard + promotion | CORRECT |
| <, >, etc. | Same, result is int | `if/then/else` pattern | CORRECT |
| &, \|, ^ | Integer promotion | Relies on ImplicitCastExpr | CORRECT |
| <<, >> | Left operand promoted | No shift-width guard | LIMITATION |
| &&, \|\| | Short-circuit | Not modeled (StrictC safe) | CORRECT |

## Regression Tests Added

- `test/c_sources/edge_cases/int_promotion.c`: 8 edge case functions
- `test/test_int_promotion.py`: Unit tests verifying CImporter handles each case
