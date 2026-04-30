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

# Files to skip
SKIP_FILES = {"test-definitions.dfy"}

def extract_info(filepath):
    modules = []
    current_module = None
    in_comment = False
    loc = 0
    with open(filepath, 'r', encoding='utf-8') as f:
        lines = f.readlines()
    for raw_line in lines:
        line = raw_line.strip()
        # Count lines of code (excluding blank lines and comments)
        if line and not line.startswith("//"):
            loc += 1
        # Very simple comment block detection (skip multi-line comments roughly)
        if "/*" in line:
            in_comment = True
        if "*/" in line:
            in_comment = False
            continue
        if in_comment:
            continue
        # Detect module start
        mod_match = re.match(r'^\s*abstract\s+module\s+(\w+)', line)
        if mod_match:
            current_module = mod_match.group(1)
            modules.append({"module": current_module, "lemmas": [], "methods": []})
            continue
        if current_module:
            # Detect lemma declarations (lemma or ghost method that are lemma-like)
            lemma_match = re.match(r'^\s*lemma\s+(\w+)', line)
            if lemma_match and 'lemma' not in line.split('//')[0].split('requires'):  # crude filter
                modules[-1]["lemmas"].append(lemma_match.group(1))
            # Detect method declarations
            meth_match = re.match(r'^\s*(?:ghost\s+)?method\s+(\w+)', line)
            if meth_match and meth_match.group(1) not in ["requires", "ensures", "modifies"]:
                modules[-1]["methods"].append(meth_match.group(1))
            # Detect lemma calls inside methods? (not strictly needed)
    return loc, modules

def main():
    folder = "."  # assume we are in dafny/
    files = sorted([f for f in os.listdir(folder) if f.endswith(".dfy") and f not in SKIP_FILES])
    print("file,module,loc_total,lemma_count,method_count,lemma_names,method_names")
    for fname in files:
        fpath = os.path.join(folder, fname)
        loc, modules = extract_info(fpath)
        if modules:
            for m in modules:
                lemma_names = ";".join(m["lemmas"])
                method_names = ";".join(m["methods"])
                print(f'{fname},{m["module"]},{loc},{len(m["lemmas"])},{len(m["methods"])},'
                      f'{lemma_names},{method_names}')
        else:
            print(f'{fname},\u2014,{loc},0,0,,')  # no module found

if __name__ == "__main__":
    main()
