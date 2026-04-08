#!/usr/bin/env python3
"""CImporter main entry point.

Reads a clang JSON AST file and emits a .lean file containing
CSimpl definitions for the Clift verification framework.

Usage:
    python3 CImporter/import.py test/clang_json/max.json -o Generated/Max.lean

This tool is in the TCB. See CImporter/README.md for the trust model.
"""

import argparse
import logging
import os
import sys

# Add parent directory to path so we can import CImporter as a package
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from CImporter.ast_parser import load_ast, parse_translation_unit
from CImporter.lean_emitter import emit_lean

log = logging.getLogger("CImporter")


def main():
    parser = argparse.ArgumentParser(
        description="CImporter: Translate clang JSON AST to Lean 4 CSimpl definitions.",
        epilog="Part of the Clift verification framework. This tool is in the TCB.",
    )
    parser.add_argument(
        "input",
        help="Path to clang JSON AST file (from clang -Xclang -ast-dump=json -fsyntax-only)",
    )
    parser.add_argument(
        "-o", "--output",
        required=True,
        help="Path to output .lean file (e.g. Generated/Max.lean)",
    )
    parser.add_argument(
        "-v", "--verbose",
        action="store_true",
        help="Enable verbose logging",
    )
    args = parser.parse_args()

    logging.basicConfig(
        level=logging.DEBUG if args.verbose else logging.INFO,
        format="%(name)s: %(levelname)s: %(message)s",
    )

    # Derive module name from output path: Generated/Max.lean -> Max
    module_name = os.path.splitext(os.path.basename(args.output))[0]
    log.info("Importing %s -> %s (module: %s)", args.input, args.output, module_name)

    # Load and parse
    ast = load_ast(args.input)
    tu = parse_translation_unit(ast)
    log.info("Parsed %d function(s)", len(tu.functions))

    # Emit
    lean_code = emit_lean(tu, module_name)

    # Write output
    os.makedirs(os.path.dirname(args.output) or ".", exist_ok=True)
    with open(args.output, 'w') as f:
        f.write(lean_code)
    log.info("Wrote %s (%d lines)", args.output, lean_code.count('\n'))


if __name__ == "__main__":
    main()
