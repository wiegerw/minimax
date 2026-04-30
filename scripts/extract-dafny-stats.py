#!/usr/bin/env python3

# Copyright 2025 - 2026 Wieger Wesselink
# Distributed under the Boost Software License, Version 1.0.
# (See accompanying file LICENSE or http://www.boost.org/LICENSE_1_0.txt)

"""
Extract verification data from Dafny files.
Usage:  python extract_dafny_stats.py   (run from the repo's dafny/ directory)
"""

import os
import re

SKIP_FILES = {"test-definitions.dfy"}

MODULE_RE = re.compile(r'^\s*abstract\s+module\s+(\w+)')
LEMMA_RE  = re.compile(r'^\s*lemma\s+(\w+)')
METHOD_RE = re.compile(r'^\s*(?:ghost\s+)?method\s+(\w+)\s*\(([^)]*)\)')

def extract_info(filepath):
    modules = []
    current_module = None
    in_block_comment = False
    loc = 0

    with open(filepath, 'r', encoding='utf-8') as f:
        for raw_line in f:
            line = raw_line.rstrip()

            # --- Handle block comments ---
            if in_block_comment:
                if "*/" in line:
                    in_block_comment = False
                continue

            if "/*" in line:
                if "*/" not in line:
                    in_block_comment = True
                continue

            stripped = line.strip()

            # --- Skip line comments and blank lines ---
            if not stripped or stripped.startswith("//"):
                continue

            # --- Count LoC ---
            loc += 1

            # --- Module detection ---
            m = MODULE_RE.match(stripped)
            if m:
                current_module = m.group(1)
                modules.append({
                    "module": current_module,
                    "lemmas": [],
                    "methods": []
                })
                continue

            if not current_module:
                continue

            # --- Lemma detection ---
            m = LEMMA_RE.match(stripped)
            if m:
                modules[-1]["lemmas"].append(m.group(1))
                continue

            # --- Method detection (with signature) ---
            m = METHOD_RE.match(stripped)
            if m:
                name, params = m.groups()
                signature = f"{name}({params.strip()})"
                modules[-1]["methods"].append(signature)

    return loc, modules

def main():
    folder = "."
    files = sorted(
        f for f in os.listdir(folder)
        if f.endswith(".dfy") and f not in SKIP_FILES
    )

    print("file,module,loc_total,lemma_count,method_count,lemma_names,method_signatures")

    for fname in files:
        loc, modules = extract_info(os.path.join(folder, fname))
        if not modules:
            print(f"{fname},—,{loc},0,0,,")
            continue

        for m in modules:
            print(
                f"{fname},{m['module']},{loc},"
                f"{len(m['lemmas'])},{len(m['methods'])},"
                f"{';'.join(m['lemmas'])},"
                f"{';'.join(m['methods'])}"
            )

if __name__ == "__main__":
    main()
