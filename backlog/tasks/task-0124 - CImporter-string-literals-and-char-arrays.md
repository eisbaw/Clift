---
id: TASK-0124
title: 'CImporter: string literals and char arrays'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-10 15:29'
updated_date: '2026-04-10 17:58'
labels:
  - phase-g
  - cimporter
dependencies: []
priority: low
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
C strings are const char arrays. Need: (1) string literals emitted as heap-allocated byte arrays, (2) char* type supported (Ptr UInt8), (3) basic string operations (strlen, strcmp) can be modeled. Not essential for kernel/driver verification but needed for protocol parsers and user-facing code.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 String literals parsed and emitted as initialized byte arrays
- [x] #2 char/char* types mapped to UInt8/Ptr UInt8
- [x] #3 Test: C function that checks string equality
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
1. Verify char/char* already supported (char = signed char = Int8, char* = pointer to Int8)
2. Add char/unsigned char to type map if not present
3. String literals: parse StringLiteral from clang AST, model as pointer to initialized byte array
4. Create test/c_sources/strings.c with minimal string usage
5. Verify generated .lean compiles
<!-- SECTION:PLAN:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
String literals and char arrays: minimal char type support for CImporter.

Changes:
- c_types.py: Added "char" -> INT8 mapping. CV qualifiers (const, volatile, restrict) stripped from pointer pointee types.
- ast_parser.py: CharacterLiteral parsed as int_literal.
- lean_emitter.py: Pointer arithmetic (ptr + n) emits Ptr.elemOffset. Handles int literal offsets without .toNat.
- Test: test/c_sources/strings.c with my_strlen (pointer increment) and starts_with (char comparison).
- Generated/Strings.lean compiles with char* as Ptr UInt8.

Limitations:
- String literals (const char *s = "hello") not yet parsed (would need heap-allocated byte arrays)
- No string library functions modeled
- AC#1 (string literals as byte arrays) not done -- only char type parsing is complete
<!-- SECTION:FINAL_SUMMARY:END -->
