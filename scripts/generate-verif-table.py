#!/usr/bin/env python3

# Copyright 2025 - 2026 Wieger Wesselink
# Distributed under the Boost Software License, Version 1.0.
# (See accompanying file LICENSE or http://www.boost.org/LICENSE_1_0.txt)

"""
Generate the combined structure + verification-time LaTeX table used in
results.tex (tab:verif-stats), directly from run-dafny.py's log files.

For each log file (e.g. logs/dafny-4.10.log), this script:
  1) parses the "Verification Report" block to get the Dafny version,
     and, for every verified file, its exit code and verification time;
  2) locates the corresponding source directory (dafny-<major.minor>,
     a sibling of the log's directory) and inspects every .dfy file in
     it (module by module) to compute LoC, lemma names and method
     signatures;
  3) writes the per-module details to logs/stats-<version>.csv (the
     same format previously produced by extract-dafny-stats.py),
     unless --skip-csv is given;
  4) optionally (--lemma-uniqueness-report) extracts every lemma's full
     body to its own file under dafny-<version>/<lemmas-dir>/ (the same
     format previously produced by export-lemmas.py), and additionally
     compares the bodies of identically-named lemmas across modules,
     writing dafny-<version>/<lemmas-dir>/REPORT.txt with the
     conclusion: whether repeated lemma names are genuine textual
     duplicates or distinct, context-sensitive specializations (see
     results.tex's claim about "systematic context-sensitive
     specialization");
  5) prints the combined LaTeX table (structure + timing) to stdout.

The first log file given determines the "canonical" structure numbers
(LoC/Lemmas/Algorithms) in the table; any later log whose structure
differs for a given file (e.g. because a workaround required
duplicated code) is flagged with a dagger, and a footnote is emitted
explaining which files and versions are affected.

Usage:
    scripts/generate-verif-table.py logs/dafny-4.10.log logs/dafny-4.11.log > logs/verif-table.tex
    scripts/generate-verif-table.py --lemma-uniqueness-report > logs/verif-table.tex

If no log files are given, logs/dafny-4.10.log and logs/dafny-4.11.log
(relative to the repository root) are used by default.
"""

import argparse
import difflib
import os
import re
import shutil
import sys
import textwrap
from pathlib import Path

# ------------------------------------------------------------
#  Configuration: presentation order of files in the LaTeX table.
# This mirrors the curated order used in results.tex (shared libraries,
# then minimax family, negamax family, TTP family, TTW family), not
# plain alphabetical order. Keep this in sync with results.tex when
# files are added, renamed, split or merged.
FILE_ORDER = [
    "definitions",
    "lemmas",
    "minimax-alpha-beta",
    "minimax",
    "negamax-alpha-beta",
    "negamax",
    "negamax-ttp",
    "negamax-ttw",
    "negamax-ttw-variants",
]

SKIP_FILES = {"test-definitions.dfy"}
# ------------------------------------------------------------

MODULE_RE = re.compile(r'^\s*abstract\s+module\s+(\w+)')
LEMMA_RE = re.compile(r'^\s*lemma\s+(\w+)')
METHOD_RE = re.compile(r'^\s*(?:ghost\s+)?method\s+(\w+)\s*\(([^)]*)\)')

LEMMA_START_RE = re.compile(r'^\s*lemma\s+(\w+)\s*\(')

REPORT_LINE_RE = re.compile(
    r'^(?P<file>\S+)\s*\|\s*Dafny\s+(?P<version>\S+)\s*\|\s*Exit\s+(?P<exit>\d+)\s*\|\s*(?P<time>[\d.]+)s'
)


def parse_arguments():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument(
        "log_files", nargs="*", type=Path,
        help="run-dafny.py log files, e.g. logs/dafny-4.10.log logs/dafny-4.11.log "
             "(default: those two, relative to the repository root)",
    )
    parser.add_argument(
        "--skip-csv", action="store_true",
        help="Do not write logs/stats-<version>.csv",
    )
    parser.add_argument(
        "--lemma-uniqueness-report", action="store_true",
        help="Also extract every lemma's full body to its own file under "
             "dafny-<version>/<lemmas-dir>/, and write a report to "
             "<lemmas-dir>/REPORT.txt analyzing whether identically-named "
             "lemmas across modules are genuine duplicates or distinct "
             "context-sensitive specializations",
    )
    parser.add_argument(
        "--lemmas-dir", default="lemmas_out",
        help="Output subdirectory name for --lemma-uniqueness-report (default: lemmas_out)",
    )
    return parser.parse_args()


def extract_info(filepath):
    """Return (loc, modules): non-blank/non-comment LoC, and a list of
    per-module {"module", "lemmas": [names], "methods": [signatures]}."""
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
                modules[-1]["methods"].append(f"{name}({params.strip()})")

    return loc, modules


def summarize(loc, modules):
    """Aggregate per-module lemma/method lists into whole-file totals."""
    return {
        "loc": loc,
        "lemmas": sum(len(m["lemmas"]) for m in modules),
        "methods": sum(len(m["methods"]) for m in modules),
    }


def write_csv(csv_path, file_entries):
    """file_entries: list of (fname, loc, modules), in the same format
    previously produced by extract-dafny-stats.py."""
    lines = ["file,module,loc_total,lemma_count,method_count,lemma_names,method_signatures"]
    for fname, loc, modules in file_entries:
        if not modules:
            lines.append(f"{fname},?,{loc},0,0,,")
            continue
        for m in modules:
            lines.append(
                f"{fname},{m['module']},{loc},"
                f"{len(m['lemmas'])},{len(m['methods'])},"
                f"{';'.join(m['lemmas'])},"
                f"{';'.join(m['methods'])}"
            )
    with open(csv_path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")


def extract_lemma_bodies(lines):
    """Return a list of (name, body_lines) for every lemma in `lines`,
    capturing the full signature and body via brace matching (so it
    works regardless of module context or how the signature wraps)."""
    lemmas = []
    i = 0
    n = len(lines)

    while i < n:
        m = LEMMA_START_RE.match(lines[i])
        if not m:
            i += 1
            continue

        name = m.group(1)
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
            if started and brace_level == 0:
                break

        lemmas.append((name, body))

    return lemmas


def collect_lemmas(dfy_paths):
    """Return {name: [(source_filename, body_lines), ...]}, across all
    given files, in the order the lemmas are encountered."""
    groups = {}
    for path in dfy_paths:
        with open(path, "r", encoding="utf-8") as f:
            lines = f.readlines()
        for name, body in extract_lemma_bodies(lines):
            groups.setdefault(name, []).append((path.name, body))
    return groups


def write_lemma_files(groups, out_dir):
    """Write every lemma occurrence in `groups` to its own file under
    out_dir, disambiguating identically-named lemmas across files with
    a "__2", "__3", ... suffix. The "__" separator can't collide with a
    real Dafny identifier, unlike a bare digit suffix (which would
    collide with, e.g., a lemma genuinely named "LoopBreakLemma2").

    out_dir is cleared of any previously exported .dfy files first, so
    a lemma that gets renamed or removed doesn't leave a stale file
    behind from an earlier run. Returns the number of lemmas written."""
    if out_dir.is_dir():
        shutil.rmtree(out_dir)
    out_dir.mkdir(parents=True)

    total = 0
    for name, occurrences in groups.items():
        for index, (_, body) in enumerate(occurrences, start=1):
            suffix = "" if index == 1 else f"__{index}"
            out_path = out_dir / f"{name}{suffix}.dfy"
            with open(out_path, "w", encoding="utf-8") as f:
                f.writelines(body)
            total += 1
    return total


def normalize_body(body_lines):
    """Normalize a lemma body for comparison: dedent (so the same lemma
    nested at different indentation levels, e.g. directly in a module
    vs. inside a class, still compares equal), strip trailing
    whitespace per line, and drop leading/trailing blank lines. This is
    a more reliable duplication test than comparing raw line counts,
    since it isn't fooled by incidental indentation or blank-line
    differences."""
    text = textwrap.dedent("".join(body_lines))
    lines = [line.rstrip() for line in text.splitlines()]
    while lines and not lines[0]:
        lines.pop(0)
    while lines and not lines[-1]:
        lines.pop()
    return "\n".join(lines)


def analyze_lemma_uniqueness(groups, version, baseline_pairs=None, baseline_version=None):
    """Compare the bodies of identically-named lemmas across modules and
    return (report_lines, exact_pairs): a short report concluding whether
    repeated lemma names are genuine textual duplicates or distinct,
    context-sensitive specializations, and the set of exact-duplicate
    (name, (file_a, file_b)) pairs found (for use as the next call's
    baseline_pairs).

    Two bodies are compared after normalize_body() (dedented,
    whitespace-trimmed) for exact equality, plus a difflib similarity
    ratio for a more nuanced measure than a blunt identical/different
    verdict.

    If baseline_pairs is given (the exact-duplicate pairs found for
    some other, "canonical" version), any exact duplicate here that
    ISN'T in baseline_pairs is annotated as new to this version -- e.g.
    because a version-specific workaround duplicated code -- rather
    than a genuine cross-module duplicate confirmed independently of
    that workaround."""
    total_lemmas = sum(len(occ) for occ in groups.values())
    repeated = {name: occ for name, occ in groups.items() if len(occ) > 1}

    lines = []
    lines.append(f"Lemma uniqueness report (Dafny {version})")
    lines.append("=" * len(lines[0]))
    lines.append(f"Total lemma instances: {total_lemmas}")
    lines.append(f"Distinct lemma names: {len(groups)}")
    lines.append(f"Names appearing more than once: {len(repeated)}")
    if baseline_pairs is not None:
        lines.append(
            f"(Exact duplicates are cross-checked against the Dafny {baseline_version} "
            f"baseline; entries marked [new here] duplicate only under Dafny {version}.)"
        )
    lines.append("")

    if not repeated:
        lines.append("No lemma name occurs more than once; nothing to compare.")
        return lines, set()

    exact_dup_groups = []  # (name, [(file_a, file_b), ...])
    exact_pairs = set()
    all_ratios = []
    detail_lines = []

    for name in sorted(repeated):
        occurrences = repeated[name]
        normalized = [normalize_body(body) for _, body in occurrences]
        sizes = [len(body) for _, body in occurrences]
        ratios = []
        name_pairs = []
        for i in range(len(normalized)):
            for j in range(i + 1, len(normalized)):
                ratio = difflib.SequenceMatcher(None, normalized[i], normalized[j]).ratio()
                ratios.append(ratio)
                if normalized[i] == normalized[j]:
                    pair_files = (occurrences[i][0], occurrences[j][0])
                    name_pairs.append(pair_files)
                    exact_pairs.add((name, tuple(sorted(pair_files))))
        all_ratios.extend(ratios)
        if name_pairs:
            exact_dup_groups.append((name, name_pairs))

        sources = [src for src, _ in occurrences]
        detail_lines.append(
            f"  {name}: {len(occurrences)}x in {sources}, "
            f"LoC {sizes}, similarity {min(ratios):.0%}-{max(ratios):.0%}"
            + (" [EXACT DUPLICATE]" if name_pairs else "")
        )

    mean_ratio = sum(all_ratios) / len(all_ratios)
    lines.append(
        f"Pairwise body similarity for repeated names, after normalizing "
        f"indentation/whitespace (0% = completely different, 100% = identical): "
        f"mean {mean_ratio:.0%}, min {min(all_ratios):.0%}, max {max(all_ratios):.0%}."
    )
    lines.append("")

    # Split findings into "confirmed" (also a duplicate in the baseline, or no
    # baseline given) vs. "new here" (only a duplicate under this version,
    # i.e. plausibly explained by a version-specific workaround).
    confirmed, new_here = [], []
    for name, pairs in exact_dup_groups:
        for a, b in pairs:
            key = (name, tuple(sorted((a, b))))
            is_new = baseline_pairs is not None and key not in baseline_pairs
            (new_here if is_new else confirmed).append((name, a, b))

    if confirmed:
        lines.append(
            f"CONCLUSION: {len({n for n, _, _ in confirmed})} repeated lemma name(s) have at "
            f"least one pair of textually identical bodies (modulo indentation/whitespace) "
            f"that is NOT explained by a version-specific workaround -- these are genuine "
            f"duplicates, not context-sensitive specializations, and are worth reviewing:"
        )
        for name, a, b in confirmed:
            lines.append(f"  - {name}: identical in {a} and {b}")
    else:
        lines.append(
            f"CONCLUSION: no repeated lemma name has a textually identical pair that isn't "
            f"already explained by a version-specific workaround -- every other repeated "
            f"name is a distinct, context-sensitive specialization (mean similarity "
            f"{mean_ratio:.0%}), supporting the claim in results.tex that these are not "
            f"textual duplicates."
        )
    if new_here:
        lines.append("")
        lines.append(
            f"{len({n for n, _, _ in new_here})} additional repeated lemma name(s) are exact "
            f"duplicates only under Dafny {version} (not under Dafny {baseline_version}) -- "
            f"consistent with the documented duplicated-code workaround, not a new finding:"
        )
        for name, a, b in new_here:
            lines.append(f"  - {name}: identical in {a} and {b} [new here]")

    lines.append("")
    lines.append("Per-lemma detail:")
    lines.extend(detail_lines)
    return lines, exact_pairs


def parse_log(log_path):
    """Return (short_version, {base_name: {time, exit}}) from a run-dafny.py log."""
    times = {}
    version = None
    in_report = False
    with open(log_path) as f:
        for line in f:
            if "Verification Report" in line:
                in_report = True
                continue
            if not in_report:
                continue
            m = REPORT_LINE_RE.match(line.strip())
            if not m:
                continue
            fname = m.group("file")
            base = fname[:-4] if fname.endswith(".dfy") else fname
            full_version = m.group("version")
            if version is None:
                version = ".".join(full_version.split(".")[:2])  # "4.10.0" -> "4.10"
            times[base] = {"time": float(m.group("time")), "exit": int(m.group("exit"))}
    if version is None:
        sys.exit(f"Error: no 'Verification Report' block found in {log_path}")
    return version, times


def fmt_name(base):
    return base.replace("_", r"\_")


def combine_filenames(bases):
    """Combine basenames sharing a common prefix into a compact shell-brace
    notation, e.g. ["negamax-ttw", "negamax-ttw-variants"] becomes
    \\texttt{negamax-ttw{,-variants}.dfy}. Falls back to an "and"-joined
    list of full names if there is no useful common prefix (or only one
    name is given)."""
    if len(bases) == 1:
        return fr"\texttt{{{fmt_name(bases[0])}.dfy}}"
    prefix = os.path.commonprefix(bases)
    if len(prefix) >= 4:
        suffixes = ",".join(b[len(prefix):] for b in bases)
        combined = fmt_name(prefix) + r"\{" + suffixes + r"\}" + ".dfy"
        return r"\texttt{" + combined + "}"
    return " and ".join(fr"\texttt{{{fmt_name(b)}.dfy}}" for b in bases)


def main():
    args = parse_arguments()

    log_paths = args.log_files
    if not log_paths:
        repo_root = Path(__file__).resolve().parent.parent
        log_paths = [repo_root / "logs" / "dafny-4.10.log", repo_root / "logs" / "dafny-4.11.log"]

    versions = []          # e.g. ["4.10", "4.11"], in the order given
    times_by_version = {}  # version -> {base: {time, exit}}
    struct_by_version = {} # version -> {base: {loc, lemmas, methods}}
    baseline_pairs = None  # exact-duplicate pairs found for the first (canonical) version
    baseline_version = None

    for log_path in log_paths:
        if not log_path.is_file():
            sys.exit(f"Error: log file not found: {log_path}")
        version, times = parse_log(log_path)
        versions.append(version)
        times_by_version[version] = times

        for base, t in times.items():
            if t["exit"] != 0:
                print(
                    f"WARNING: {base}.dfy did NOT verify under Dafny {version} "
                    f"(exit code {t['exit']}, {t['time']:.2f}s) -- its time in the table is "
                    f"from a failed run, not a real verification",
                    file=sys.stderr,
                )

        src_dir = log_path.resolve().parent.parent / f"dafny-{version}"
        if not src_dir.is_dir():
            sys.exit(f"Error: source directory not found: {src_dir}")

        dfy_files = sorted(
            f for f in os.listdir(src_dir) if f.endswith(".dfy") and f not in SKIP_FILES
        )
        file_entries = []  # (fname, loc, modules), for the CSV
        struct = {}
        for fname in dfy_files:
            loc, modules = extract_info(src_dir / fname)
            file_entries.append((fname, loc, modules))
            struct[fname[:-4]] = summarize(loc, modules)
        struct_by_version[version] = struct

        if not args.skip_csv:
            csv_path = log_path.resolve().parent / f"stats-{version}.csv"
            write_csv(csv_path, file_entries)
            print(f"Wrote {csv_path}", file=sys.stderr)

        if args.lemma_uniqueness_report:
            all_dfy_files = sorted(f for f in os.listdir(src_dir) if f.endswith(".dfy"))
            groups = collect_lemmas([src_dir / f for f in all_dfy_files])

            lemmas_dir = src_dir / args.lemmas_dir
            count = write_lemma_files(groups, lemmas_dir)
            print(f"Wrote {count} lemmas to {lemmas_dir}/", file=sys.stderr)

            report_lines, exact_pairs = analyze_lemma_uniqueness(
                groups, version, baseline_pairs, baseline_version
            )
            if baseline_pairs is None:
                baseline_pairs, baseline_version = exact_pairs, version

            report_path = lemmas_dir / "REPORT.txt"
            with open(report_path, "w", encoding="utf-8") as f:
                f.write("\n".join(report_lines) + "\n")
            print(f"--- {report_path} ---", file=sys.stderr)
            print("\n".join(report_lines), file=sys.stderr)

    canonical = versions[0]
    canonical_struct = struct_by_version[canonical]

    # Files whose structure differs from the canonical version in some other
    # version. Split into two kinds: files where only LoC differs (the
    # lemma/method counts -- and so the underlying proof content -- match, so
    # the difference is pure restructuring overhead, e.g. extra modules/imports
    # needed to avoid `refines`) versus files where lemma/method counts also
    # differ (genuine duplicated proof content).
    flagged = []
    flagged_content_differs = []
    for base in FILE_ORDER:
        s0 = canonical_struct.get(base)
        if s0 is None:
            continue
        for v in versions[1:]:
            s = struct_by_version[v].get(base)
            if s is not None and s != s0:
                flagged.append(base)
                if s["lemmas"] != s0["lemmas"] or s["methods"] != s0["methods"]:
                    flagged_content_differs.append(base)
                break

    latex = []
    latex.append(r"\begin{table}[t]")
    latex.append(r"\centering")
    version_list = " and ".join(f"Dafny~{v}" for v in versions)
    latex.append(fr"\caption{{Structure and verification times (seconds) of the Dafny verification artefact, for {version_list}.}}")
    latex.append(r"\label{tab:verif-stats}")
    latex.append(r"\small")
    col_spec = " ".join(["l", "r", "c", "c"] + ["r"] * len(versions))
    latex.append(fr"\begin{{tabular}}{{@{{}}{col_spec}@{{}}}}")
    latex.append(r"\toprule")
    time_cols = "\\multicolumn{" + str(len(versions)) + "}{c}{\\textbf{Time (s)}}"
    latex.append(fr" & \multicolumn{{3}}{{c}}{{\textbf{{Structure}}}} & {time_cols} \\")
    time_col_start = 5
    time_col_end = 4 + len(versions)
    latex.append(fr"\cmidrule(lr){{2-4}} \cmidrule(lr){{{time_col_start}-{time_col_end}}}")
    version_headers = " & ".join(fr"\textbf{{{v}}}" for v in versions)
    latex.append(fr"\textbf{{File}} & \textbf{{LoC}} & \textbf{{Lemmas}} & \textbf{{Algorithms}} & {version_headers} \\")
    latex.append(r"\midrule")

    for base in FILE_ORDER:
        s0 = canonical_struct.get(base)
        if s0 is None:
            print(f"Warning: '{base}.dfy' not found in {canonical} report", file=sys.stderr)
            continue
        dagger = r"$^{\dagger}$" if base in flagged else ""
        time_values = []
        for v in versions:
            t = times_by_version[v].get(base)
            if t is None:
                time_values.append("--")
            elif t["exit"] != 0:
                time_values.append("FAIL")
            else:
                time_values.append(f"{t['time']:.2f}")
        row = fr"\texttt{{{fmt_name(base)}.dfy}}{dagger} & {s0['loc']} & {s0['lemmas']} & {s0['methods']}"
        row += " & " + " & ".join(time_values) + r" \\"
        latex.append(row)

    latex.append(r"\midrule")
    latex.append(r"\textit{NegamaxTTM (Marsland)} & -- & -- & --" + " & --" * len(versions) + r" \\")
    latex.append(r"\bottomrule")
    latex.append(r"\end{tabular}")

    if flagged:
        content_differs = [b for b in flagged if b in flagged_content_differs]
        loc_only = [b for b in flagged if b not in flagged_content_differs]
        other_versions = " and ".join(f"Dafny~{v}" for v in versions[1:])
        latex.append(r"\vspace{2mm}")
        latex.append(r"\par\noindent\footnotesize\raggedright")
        notes = []
        if content_differs:
            names = combine_filenames(content_differs)
            notes.append(
                fr"$^{{\dagger}}$Under {other_versions}, {names} required a modified version with "
                r"duplicated code to work around an internal tool error; the LoC/Lemmas/Algorithms "
                fr"columns report the original (Dafny~{canonical}) structure, while the "
                fr"{other_versions} time reflects the duplicated version."
            )
        if loc_only:
            names = combine_filenames(loc_only)
            notes.append(
                fr"$^{{\dagger}}$Under {other_versions}, {names} required additional supporting "
                r"modules (sharing code via \texttt{import opened} instead of \texttt{refines}) to "
                r"work around an internal tool error; this accounts for the modest increase in LoC, "
                r"while the Lemmas/Algorithms counts -- and the underlying proofs -- are unchanged."
            )
        latex.append(" ".join(notes))

    latex.append(r"\end{table}")

    print("\n".join(latex))


if __name__ == "__main__":
    main()
