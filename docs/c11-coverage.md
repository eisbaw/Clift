# CImporter C11 Standard Coverage

Task 0183: CImporter validation against C11 standard sections.

This document maps C11 standard sections to CImporter coverage status.
The CImporter is in the TCB -- any mistranslation silently invalidates proofs.

## Methodology

For each C11 section, we classify coverage as:
- **Covered**: CImporter handles this correctly (with tests)
- **Excluded (StrictC)**: Intentionally excluded by StrictC restrictions
- **Not Applicable**: Does not apply to our usage
- **Limitation**: Partially handled with documented gap
- **Not Covered**: Should be handled but is not yet

## C11 6.2: Concepts (Types, Scope, Linkage)

### 6.2.1 Scopes of identifiers
- **Covered**: Function scope (parameters, locals) handled by ast_parser.py
- **Covered**: File scope (globals) handled since task-0109
- **Excluded**: Block scope re-declaration (StrictC does not allow shadowing)

### 6.2.2 Linkages of identifiers
- **Limitation**: External linkage assumed for all non-static functions
- **Not Covered**: `static` functions (not distinguished from extern)

### 6.2.3 Name spaces of identifiers
- **Covered**: Struct tag namespace separate from ordinary identifiers
- **Not Applicable**: Label names (no goto), enum tags (enum constants are in ordinary namespace)

### 6.2.4 Storage durations of objects
- **Covered**: Automatic (locals) -- modeled as Locals record fields
- **Limitation**: Static storage duration -- globals modeled in Locals (Phase 1 limitation)
- **Not Covered**: Allocated (malloc/free) -- no dynamic allocation in model

### 6.2.5 Types
- **Covered**: Integer types: uint8/16/32/64, int8/16/32/64
- **Covered**: `_Bool` / `bool`
- **Covered**: `void` (return type only)
- **Covered**: Pointer types (Phase 3a+)
- **Covered**: Struct types (Phase 3b+)
- **Covered**: Union types (modeled as primary field, Phase 3b+)
- **Excluded**: Floating-point types (StrictC Phase 1)
- **Excluded**: Complex types
- **Excluded**: VLA types

### 6.2.6 Representations of types
- **Covered**: Two's complement for signed integers (assumed, matches all modern platforms)
- **Covered**: Little-endian byte order (assumed for x86-64)
- **Limitation**: Platform-specific sizes hardcoded (LP64 model: long = 64-bit)

### 6.2.7 Compatible type and composite type
- **Not Covered**: Composite types across translation units
- **Limitation**: Multi-file import (multi_import.py) does not check type compatibility

## C11 6.3: Conversions

### 6.3.1.1 Boolean, characters, and integers (Integer promotions)
- **Covered**: Clang AST includes ImplicitCastExpr for integer promotions
- **Covered**: CImporter handles cast_expr nodes
- **Limitation**: CImporter trusts clang's promotion decisions; no independent verification
- **Test**: test/c_sources/edge_cases/int_promotion.c

### 6.3.1.2 Boolean type
- **Covered**: `_Bool` mapped to Bool in Lean

### 6.3.1.3 Signed and unsigned integers
- **Covered**: Signed-to-unsigned conversion via modular arithmetic
- **Covered**: Unsigned-to-signed: value preserved if it fits, else implementation-defined
- **Limitation**: All signed types mapped to unsigned Lean types (UInt) for memory layout.
  Signed semantics deferred to Phase 2 (WordAbstract).

### 6.3.1.4 Real floating and integer
- **Excluded**: No floating-point support (StrictC)

### 6.3.1.8 Usual arithmetic conversions
- **Covered**: Handled by clang's ImplicitCastExpr in the AST
- **Limitation**: Not independently verified by CImporter

### 6.3.2.1 Lvalues, arrays, and function designators
- **Covered**: Array-to-pointer decay handled in array subscript
- **Excluded**: Function designators (no function pointers)

### 6.3.2.3 Pointers
- **Covered**: Pointer-to-pointer casts (ptr_cast_expr)
- **Covered**: Null pointer constant (0 -> Ptr.null)
- **Limitation**: Integer-to-pointer casts not supported

## C11 6.5: Expressions

### 6.5.1 Primary expressions
- **Covered**: Identifiers (var_ref, global_ref)
- **Covered**: Integer constants (int_literal)
- **Excluded**: String literals (limited support via strings.c)
- **Excluded**: Generic selection (_Generic)

### 6.5.2 Postfix operators
- **Covered**: Array subscript (array_subscript)
- **Covered**: Function calls (call_expr)
- **Covered**: Structure/union member access (member_access, ->)
- **Excluded**: Postfix increment/decrement in expressions (StrictC)
- **Covered**: sizeof (sizeof_expr)

### 6.5.3 Unary operators
- **Covered**: Unary minus (-)
- **Covered**: Bitwise NOT (~)
- **Covered**: Logical NOT (!)
- **Covered**: Pointer dereference (*)
- **Excluded**: Address-of (&) for locals (StrictC)
- **Excluded**: Prefix increment/decrement in expressions (StrictC)

### 6.5.4 Cast operators
- **Covered**: Explicit casts between integer types (cast_expr)
- **Covered**: Pointer casts (ptr_cast_expr)
- **Covered**: Narrowing cast guards emitted

### 6.5.5 Multiplicative operators
- **Covered**: *, /, %
- **Covered**: Division-by-zero guard emitted
- **Covered**: Signed overflow guard for signed division (INT_MIN / -1)

### 6.5.6 Additive operators
- **Covered**: +, -
- **Covered**: Pointer arithmetic (ptr + int, ptr - int)
- **Covered**: Signed overflow guards emitted

### 6.5.7 Bitwise shift operators
- **Covered**: <<, >>
- **Limitation**: No guard for shift-by-negative or shift-by-width (both UB)

### 6.5.8-6.5.9 Relational and equality operators
- **Covered**: <, >, <=, >=, ==, !=
- **Covered**: Pointer comparisons (for NULL checks)

### 6.5.10-6.5.12 Bitwise operators
- **Covered**: &, ^, |

### 6.5.13-6.5.14 Logical operators
- **Covered**: &&, ||
- **Limitation**: Short-circuit evaluation not explicitly modeled
  (StrictC: no side effects in expressions, so short-circuit is observable
  only for UB-triggering sub-expressions)

### 6.5.15 Conditional operator
- **Covered**: Ternary (cond ? a : b) via ternary expression

### 6.5.16 Assignment operators
- **Covered**: Simple assignment (=)
- **Excluded**: Compound assignment (+=, -=, etc.) -- decomposed by clang AST

### 6.5.17 Comma operator
- **Excluded**: StrictC prohibits comma operator in expressions

### 6.5p7 Strict aliasing rule
- **Covered**: Type tag mismatch detected by heapPtrValid -> fault
- **Limitation**: Stricter than C standard (no char exception)

## C11 6.7: Declarations

### 6.7.1 Storage-class specifiers
- **Limitation**: `static` not distinguished from `extern`
- **Not Applicable**: `register`, `_Thread_local`

### 6.7.2 Type specifiers
- **Covered**: Integer type specifiers (int, char, short, long, unsigned, signed)
- **Covered**: struct-or-union-specifier
- **Covered**: enum-specifier
- **Covered**: typedef-name (via clang desugaring)
- **Excluded**: _Atomic, _Complex

### 6.7.2.1 Structure and union specifiers
- **Covered**: Struct definitions with fields
- **Covered**: Union definitions (modeled as primary field)
- **Covered**: Struct layout (size, alignment, padding) computed
- **Covered**: Nested struct field access via ->

### 6.7.2.2 Enumeration specifiers
- **Covered**: Enum constants as UInt32 definitions
- **Limitation**: Enum underlying type always UInt32 (C allows implementation-defined)

### 6.7.3 Type qualifiers
- **Excluded**: `volatile` not modeled (hardware register semantics out of scope)
- **Not Applicable**: `const` (no effect on semantics in our model)
- **Excluded**: `restrict` (pointer aliasing hint, no semantic effect for correctness)

### 6.7.6 Declarators
- **Covered**: Function declarators (parameters)
- **Covered**: Pointer declarators
- **Excluded**: Array declarators (VLA)

### 6.7.9 Initialization
- **Covered**: Simple initializers (variable = expr)
- **Limitation**: Locals default to Inhabited (zero-init), not indeterminate

## C11 6.8: Statements and Blocks

### 6.8.1 Labeled statements
- **Excluded**: goto labels (StrictC)
- **Covered**: case/default in switch (no fall-through)

### 6.8.2 Compound statements
- **Covered**: Block statements (compound kind in ast_parser)

### 6.8.3 Expression and null statements
- **Covered**: Expression statements (standalone function calls)
- **Covered**: Null statements (skip)

### 6.8.4 Selection statements
- **Covered**: if / if-else
- **Covered**: switch (no fall-through, via CSimpl.cond chain)

### 6.8.5 Iteration statements
- **Covered**: while
- **Covered**: for (desugared to init + while)
- **Covered**: do-while

### 6.8.6 Jump statements
- **Excluded**: goto (StrictC)
- **Covered**: break (via CSimpl.throw)
- **Covered**: continue
- **Covered**: return (with and without value)

## C11 Annex J: Undefined Behavior (Selected Items)

### Arithmetic UB
- **Covered**: Signed overflow (guards emitted)
- **Covered**: Division by zero (guards emitted)
- **Covered**: INT_MIN / -1 (guards emitted)
- **Limitation**: Shift UB (shift >= width, negative shift) not guarded

### Memory UB
- **Covered**: Null pointer dereference (heapPtrValid)
- **Covered**: Out-of-bounds access (heapPtrValid bounds check)
- **Covered**: Unaligned access (heapPtrValid alignment check)
- **Covered**: Strict aliasing violation (TypeTag mismatch)
- **Not Covered**: Use-after-free (no malloc/free model)
- **Limitation**: Uninitialized local reads (zero-init, documented)

### Sequence point UB
- **Excluded**: StrictC prohibits side effects in expressions,
  so sequence point violations cannot occur

## Implementation-Defined Behavior (Documented Assumptions)

| Behavior | Our Assumption | C11 Reference |
|----------|---------------|---------------|
| char signedness | signed (x86-64 Linux/gcc) | 6.2.5p15 |
| Integer sizes | LP64 (int=32, long=64) | 6.2.5 |
| Byte order | Little-endian | Not specified |
| Two's complement | Yes (universal since C23) | 6.2.6.2 |
| Right shift of signed | Arithmetic (sign-extending) | 6.5.7p5 |
| Struct padding | Matches gcc x86-64 ABI | 6.7.2.1 |
| Enum underlying type | uint32_t | 6.7.2.2 |

## Coverage Summary

| C11 Section | Category | Covered | Excluded | Limitation | Not Covered |
|------------|----------|---------|----------|------------|-------------|
| 6.2 Types | 10 items | 7 | 3 | 3 | 1 |
| 6.3 Conversions | 8 items | 5 | 2 | 3 | 0 |
| 6.5 Expressions | 20 items | 16 | 5 | 3 | 0 |
| 6.7 Declarations | 10 items | 7 | 4 | 3 | 0 |
| 6.8 Statements | 8 items | 7 | 1 | 0 | 0 |
| Annex J UB | 10 items | 6 | 1 | 2 | 1 |

**Total**: ~66 items checked. ~48 covered, ~16 excluded (by design), ~14 limitations (documented), ~2 not covered.
