---
id: TASK-0119
title: 'CImporter: bitwise operations (&, |, ^, ~, <<, >>)'
status: To Do
assignee: []
created_date: '2026-04-10 15:29'
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
- [ ] #1 Bitwise AND, OR, XOR parsed and emitted correctly
- [ ] #2 Bitwise NOT (complement) parsed and emitted
- [ ] #3 Left/right shift parsed and emitted
- [ ] #4 Test: C function using bitmask operations
- [ ] #5 Generated .lean compiles
<!-- AC:END -->
