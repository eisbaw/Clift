#!/usr/bin/env python3
"""Differential test: compare CImporter struct layout against gcc.

Compiles test/c_sources/struct_sizes.c with gcc, runs it to get sizeof/offsetof,
then parses the same structs with CImporter and verifies the computed layout matches.

This is risk mitigation for Risk #7 in plan.md:
  "Silent semantic mismatch between our heap model and what gcc actually does
   for struct layout/padding would invalidate all pointer proofs."

Usage:
    python3 test/test_struct_layout.py
"""

import json
import os
import subprocess
import sys
import tempfile

# Add project root to path
project_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, project_root)

from CImporter.c_types import (
    StructDef, StructField, compute_struct_layout, register_struct,
    clear_struct_defs, get_struct_defs, type_size_align,
    UINT8, UINT16, UINT32, UINT64, INT32, CType,
)


def get_gcc_layout(c_source_path: str) -> dict:
    """Compile struct_sizes.c with gcc, run it, parse output.

    Returns:
        dict mapping struct_name -> {
            'size': int, 'align': int,
            'fields': dict mapping field_name -> offset
        }
    """
    with tempfile.NamedTemporaryFile(suffix='.out', delete=False) as f:
        binary_path = f.name

    try:
        # Compile
        result = subprocess.run(
            ['gcc', '-o', binary_path, c_source_path],
            capture_output=True, text=True, timeout=30
        )
        if result.returncode != 0:
            print(f"FAIL: gcc compilation failed:\n{result.stderr}", file=sys.stderr)
            sys.exit(1)

        # Run
        result = subprocess.run(
            [binary_path],
            capture_output=True, text=True, timeout=10
        )
        if result.returncode != 0:
            print(f"FAIL: struct_sizes binary failed:\n{result.stderr}", file=sys.stderr)
            sys.exit(1)

        # Parse output
        structs = {}
        for line in result.stdout.strip().split('\n'):
            parts = line.split()
            if parts[0] == 'STRUCT':
                name = parts[1]
                size = int(parts[2])
                align = int(parts[3])
                if name not in structs:
                    structs[name] = {'size': size, 'align': align, 'fields': {}}
                else:
                    structs[name]['size'] = size
                    structs[name]['align'] = align
            elif parts[0] == 'FIELD':
                name = parts[1]
                field = parts[2]
                offset = int(parts[3])
                if name not in structs:
                    structs[name] = {'size': 0, 'align': 0, 'fields': {}}
                structs[name]['fields'][field] = offset

        return structs
    finally:
        if os.path.exists(binary_path):
            os.unlink(binary_path)


def build_cimporter_layout() -> dict:
    """Compute struct layouts using CImporter's layout algorithm.

    Returns same format as get_gcc_layout.
    """
    clear_struct_defs()

    # Helper to create a pointer-to-struct CType
    def ptr_to(struct_name: str) -> CType:
        return CType(
            name=f"struct {struct_name} *",
            signed=False, bits=0,
            is_pointer=True,
            pointee=CType(
                name=f"struct {struct_name}",
                signed=False, bits=0,
                is_struct=True, struct_name=struct_name,
            ),
        )

    # Define test structs matching struct_sizes.c
    test_structs = [
        StructDef(name="simple", fields=[
            StructField(name="a", c_type=UINT32),
            StructField(name="b", c_type=UINT32),
        ]),
        StructDef(name="padded", fields=[
            StructField(name="x", c_type=UINT8),
            StructField(name="y", c_type=UINT32),
        ]),
        StructDef(name="node", fields=[
            StructField(name="val", c_type=INT32),
            StructField(name="next", c_type=ptr_to("node")),
        ]),
        StructDef(name="mixed", fields=[
            StructField(name="a", c_type=UINT8),
            StructField(name="b", c_type=UINT16),
            StructField(name="c", c_type=UINT32),
            StructField(name="d", c_type=UINT64),
        ]),
        StructDef(name="trailing_pad", fields=[
            StructField(name="x", c_type=UINT64),
            StructField(name="y", c_type=UINT8),
        ]),
        StructDef(name="ptr_pair", fields=[
            StructField(name="a", c_type=ptr_to("uint32_t")),
            StructField(name="b", c_type=ptr_to("uint32_t")),
        ]),
    ]

    result = {}
    for sdef in test_structs:
        compute_struct_layout(sdef)
        register_struct(sdef)
        fields = {}
        for f in sdef.fields:
            fields[f.name] = f.offset
        result[sdef.name] = {
            'size': sdef.total_size,
            'align': sdef.alignment,
            'fields': fields,
        }

    return result


def main():
    c_source = os.path.join(project_root, "test", "c_sources", "struct_sizes.c")
    if not os.path.exists(c_source):
        print(f"FAIL: {c_source} not found", file=sys.stderr)
        sys.exit(1)

    print("=== Differential test: struct layout vs gcc ===")
    print()

    # Get gcc results
    print("Compiling and running struct_sizes.c with gcc...")
    gcc_layout = get_gcc_layout(c_source)
    print(f"  Got layout for {len(gcc_layout)} structs from gcc")

    # Get CImporter results
    print("Computing layout with CImporter...")
    cimporter_layout = build_cimporter_layout()
    print(f"  Got layout for {len(cimporter_layout)} structs from CImporter")

    # Compare
    print()
    failures = 0
    for struct_name in sorted(gcc_layout.keys()):
        gcc = gcc_layout[struct_name]
        if struct_name not in cimporter_layout:
            print(f"FAIL: struct {struct_name} not in CImporter output")
            failures += 1
            continue

        ci = cimporter_layout[struct_name]

        # Check size
        if gcc['size'] != ci['size']:
            print(f"FAIL: struct {struct_name} size: gcc={gcc['size']}, cimporter={ci['size']}")
            failures += 1
        else:
            print(f"OK:   struct {struct_name} size={gcc['size']}")

        # Check alignment
        if gcc['align'] != ci['align']:
            print(f"FAIL: struct {struct_name} align: gcc={gcc['align']}, cimporter={ci['align']}")
            failures += 1
        else:
            print(f"OK:   struct {struct_name} align={gcc['align']}")

        # Check field offsets
        for field_name in sorted(gcc['fields'].keys()):
            gcc_offset = gcc['fields'][field_name]
            if field_name not in ci['fields']:
                print(f"FAIL: struct {struct_name}.{field_name} not in CImporter output")
                failures += 1
                continue
            ci_offset = ci['fields'][field_name]
            if gcc_offset != ci_offset:
                print(f"FAIL: struct {struct_name}.{field_name} offset: gcc={gcc_offset}, cimporter={ci_offset}")
                failures += 1
            else:
                print(f"OK:   struct {struct_name}.{field_name} offset={gcc_offset}")

    print()
    if failures > 0:
        print(f"FAILED: {failures} mismatch(es) found!")
        sys.exit(1)
    else:
        print(f"PASSED: All struct sizes and offsets match gcc.")
        sys.exit(0)


if __name__ == "__main__":
    main()
