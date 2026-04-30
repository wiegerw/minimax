#!/usr/bin/env python3

# Copyright 2026 Wieger Wesselink
# Distributed under the Boost Software License, Version 1.0.
# (See accompanying file LICENSE or http://www.boost.org/LICENSE_1_0.txt)

import os
import re
from collections import defaultdict

OUTPUT_DIR = "lemmas_out"

lemma_start_re = re.compile(r'^\s*lemma\s+(\w+)\s*\(')

def read_file(path):
    with open(path, "r", encoding="utf-8") as f:
        return f.readlines()

def extract_lemmas(lines):
    """
    Returns list of (name, body_lines)
    """
    lemmas = []
    i = 0
    n = len(lines)

    while i < n:
        line = lines[i]

        m = lemma_start_re.match(line)
        if not m:
            i += 1
            continue

        name = m.group(1)

        # Capture full lemma body using brace matching
        body = []
        brace_level = 0
        started = False

        while i < n:
            line = lines[i]
            body.append(line)

            brace_level += line.count("{")
            brace_level -= line.count("}")

            if "{" in line:
                started = True

            i += 1

            # end when braces close AND we have started
            if started and brace_level == 0:
                break

        lemmas.append((name, body))

    return lemmas


def write_lemmas(files):
    os.makedirs(OUTPUT_DIR, exist_ok=True)

    counters = defaultdict(int)

    for file in files:
        lines = read_file(file)
        lemmas = extract_lemmas(lines)

        for name, body in lemmas:
            counters[name] += 1
            suffix = "" if counters[name] == 1 else str(counters[name])
            out_name = f"{name}{suffix}.dfy"
            out_path = os.path.join(OUTPUT_DIR, out_name)

            with open(out_path, "w", encoding="utf-8") as f:
                f.writelines(body)

    print(f"Wrote {sum(counters.values())} lemmas to {OUTPUT_DIR}/")


def main():
    files = [f for f in os.listdir(".") if f.endswith(".dfy")]
    write_lemmas(files)

if __name__ == "__main__":
    main()
