#!/usr/bin/env python3

# Copyright 2025 - 2026 Wieger Wesselink
# Distributed under the Boost Software License, Version 1.0.
# (See accompanying file LICENSE or http://www.boost.org/LICENSE_1_0.txt)

#!/usr/bin/env python3
"""
Extract verification data from Dafny files.
Outputs:
  1) Full CSV (same as before)
  2) Aggregated LaTeX table for families (no timing)
"""

import os, re

# ------------------------------------------------------------
#  Configuration: families for the LaTeX table.
# Each family is (name, list of file basenames without .dfy).
FAMILIES = [
    ("Shared libraries",           ["definitions", "lemmas"]),
    ("Minimax variants",           ["minimax", "minimax-alpha-beta"]),
    ("Negamax variants",           ["negamax", "negamax-alpha-beta"]),
    ("Depth-limited negamax",      ["negamax-depth-limited"]),
    ("NegamaxTTW (Wikipedia)",     ["negamax-ttw"]),
    ("NegamaxTTW variants",        ["negamax-ttw-variants"]),
    # NegamaxTTM has no verified Dafny code; added manually.
]
# ------------------------------------------------------------

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
            if in_block_comment:
                if "*/" in line:
                    in_block_comment = False
                continue
            if "/*" in line:
                if "*/" not in line:
                    in_block_comment = True
                continue
            stripped = line.strip()
            if not stripped or stripped.startswith("//"):
                continue
            loc += 1

            m = MODULE_RE.match(stripped)
            if m:
                current_module = m.group(1)
                modules.append({"module": current_module, "lemmas": [], "methods": []})
                continue
            if not current_module:
                continue
            m = LEMMA_RE.match(stripped)
            if m:
                modules[-1]["lemmas"].append(m.group(1))
                continue
            m = METHOD_RE.match(stripped)
            if m:
                name, params = m.groups()
                signature = f"{name}({params.strip()})"
                modules[-1]["methods"].append(signature)
    return loc, modules

def main():
    # 1) Collect per\u2011file data and print CSV
    file_data = {}
    csv_lines = ["file,module,loc_total,lemma_count,method_count,lemma_names,method_signatures"]
    files = sorted(
        [f for f in os.listdir(".") if f.endswith(".dfy") and f not in SKIP_FILES]
    )

    for fname in files:
        path = os.path.join(".", fname)
        loc, modules = extract_info(path)
        base = fname[:-4]  # without .dfy
        lemmas_total = sum(len(m["lemmas"]) for m in modules)
        methods_total = sum(len(m["methods"]) for m in modules)
        file_data[base] = {
            "loc": loc,
            "lemmas": lemmas_total,
            "methods": methods_total,
            "modules": modules,
        }
        if not modules:
            csv_lines.append(f"{fname},?,{loc},0,0,,")
        else:
            for m in modules:
                csv_lines.append(
                    f"{fname},{m['module']},{loc},"
                    f"{len(m['lemmas'])},{len(m['methods'])},"
                    f"{';'.join(m['lemmas'])},"
                    f"{';'.join(m['methods'])}"
                )

    # Print CSV
    print("\n".join(csv_lines))
    print()  # blank line

    # 2) Build LaTeX table (no timing)
    latex = []
    latex.append(r"\begin{table}[t]")
    latex.append(r"\centering")
    latex.append(r"\caption{Structure of the Dafny verification artefact.}")
    latex.append(r"\label{tab:verif-stats}")
    latex.append(r"\small")
    latex.append(r"\begin{tabular}{@{}l r r r@{}}")
    latex.append(r"\toprule")
    latex.append(r"\textbf{File / module family} & \textbf{LoC} & \textbf{Lemmas} & \textbf{Methods} \\")
    latex.append(r"\midrule")

    for family_name, bases in FAMILIES:
        total_loc = 0
        total_lemmas = 0
        total_methods = 0
        for b in bases:
            if b in file_data:
                total_loc += file_data[b]["loc"]
                total_lemmas += file_data[b]["lemmas"]
                total_methods += file_data[b]["methods"]
        latex.append(fr"{family_name} & {total_loc} & {total_lemmas} & {total_methods} \\")

    # NegamaxTTM row
    latex.append(r"\midrule")
    latex.append(r"\textit{NegamaxTTM (Marsland)} & -- & -- & -- \\")
    latex.append(r"\bottomrule")
    latex.append(r"\end{tabular}")
    latex.append(r"\end{table}")

    print("\n".join(latex))

if __name__ == "__main__":
    main()
