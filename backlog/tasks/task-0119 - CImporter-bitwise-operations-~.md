---
id: TASK-0119
title: 'CImporter: bitwise operations (&, |, ^, ~, <<, >>)'
status: Done
assignee:
  - '@claude'
created_date: '2026-04-10 15:29'
updated_date: '2026-04-10 17:34'
labels:
  - phase-g
  - cimporter
  - industrial
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Real embedded C uses bitwise ops extensively for register manipulation, flag checking, protocol parsing. Our CImporter handles arithmetic but not bitwise ops as separate operations. Need: (1) parse BinaryOperator with &,|,^,<<,>> opcodes, (2) parse UnaryOperator with ~ opcode, (3) emit Lean 4 UInt32.land/lor/lxor/shiftLeft/shiftRight/complement, (4) BitVec lemmas for WordAbstract to lift these to Nat-level. Essential for any hardware-adjacent C.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 Bitwise AND, OR, XOR parsed and emitted correctly
- [x] #2 Bitwise NOT (complement) parsed and emitted
- [x] #3 Left/right shift parsed and emitted
- [x] #4 Test: C function using bitmask operations
- [x] #5 Generated .lean compiles
<!-- AC:END -->

## Implementation Plan

<!-- SECTION:PLAN:BEGIN -->
$1. Create test/c_sources/bitwise.c with bitmask operations\n2. Run CImporter, verify parsing and emission\n3. Verify generated .lean compiles\n4. Mark ACs complete
<!-- SECTION:PLAN:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
$Bitwise operations (&, |, ^, ~, <<, >>) were already parsed and emitted correctly by the CImporter.\n\nChanges:\n- Added test/c_sources/bitwise.c with 5 bitmask functions (extract_bits, set_bit, clear_bit, toggle_bit, combine_halves)\n- Generated/Bitwise.lean compiles successfully with Lean operators &&&, |||, ^^^, <<<, >>>, ~~~\n- Added to lakefile.lean and Justfile import-all\n\nThe implementation was already complete in ast_parser.py (supported_ops) and lean_emitter.py (lean_op map). This task validated correctness with a real test.
<!-- SECTION:FINAL_SUMMARY:END -->
