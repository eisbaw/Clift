# CImporter

Translates clang JSON AST output into Lean 4 CSimpl definitions.

## Trust Model

This tool is in the TCB (Trusted Computing Base). If it mistranslates C to CSimpl,
proofs will be about the wrong program. This is the same trust model as seL4's StrictC parser.

Mitigation: extensive regression tests, snapshot testing, differential testing against
known C semantics edge cases.

## Usage

```bash
just import test/c_sources/gcd.c Gcd
```

## Supported C Subset (StrictC)

- Integer types: uint8_t, uint16_t, uint32_t, uint64_t, int8_t, ... int64_t
- Local variables, function parameters
- if/else, while, for (desugared to while)
- return, break, continue
- Arithmetic: +, -, *, /, %, comparisons
- Bitwise: &, |, ^, <<, >>
- Pointer dereference (single indirection)
- Struct field access (. and ->)
- Array indexing

## NOT Supported

- Floating point
- goto, longjmp, switch fall-through
- Address-of local variables (&local)
- Side effects in expressions
- Variadic functions, VLAs
- Pre/post increment in expressions
