#!/usr/bin/env python3

# Copyright 2025 - 2026 Wieger Wesselink
# Distributed under the Boost Software License, Version 1.0.
# (See accompanying file LICENSE or http://www.boost.org/LICENSE_1_0.txt)

import argparse
import os
import re
import subprocess
import sys
import time
from pathlib import Path
from typing import List, Optional, Tuple


def parse_arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Run Dafny verification for all installed versions.")
    parser.add_argument("dafny_files", nargs="+", help="Dafny source files to verify")
    parser.add_argument("--verify-dependencies", action="store_true", help="Enable verification of included files")
    parser.add_argument("--verbosity", type=int, help="Set Dafny verbosity level (e.g., 1, 2, 3)")
    parser.add_argument("--show-dafny-output", action="store_true", help="Print Dafny verifier output")
    parser.add_argument("--forbid-assume", action="store_true", help="Disallow 'assume' statements in Dafny source")
    parser.add_argument("--latest", action="store_true", help="Use the latest Dafny version instead of all installed versions")
    parser.add_argument("--version", help="Only runs with Dafny versions matching this regex pattern")
    parser.add_argument("--exclude", help="Skip Dafny files matching this regex pattern")
    return parser.parse_args()


def find_dafny_extension_dir() -> Optional[Path]:
    home = Path.home()
    extension_dirs = [
        home / ".vscode/extensions",
        home / ".var/app/com.visualstudio.code/data/vscode/extensions",
        home / ".config/Code/extensions",
        home / ".vscode-server/extensions",
        home / ".vscode-remote/extensions",
    ]
    for ext_dir in extension_dirs:
        if not ext_dir.is_dir():
            continue
        matches = sorted(ext_dir.glob("dafny-lang.ide-vscode*"))
        if matches:
            return matches[-1]
    return None


def find_dafny_versions(resources_dir: Path, latest=False, version_pattern: Optional[str] = None) -> List[Tuple[str, Path]]:
    versioned_dafny = []
    path_pattern = re.compile(r'/resources/([0-9.]+)/github/dafny/dafny')

    for path in resources_dir.rglob("dafny"):
        if path.is_file() and os.access(path, os.X_OK):
            match = path_pattern.search(str(path))
            if match:
                version_str = match.group(1)
                if version_pattern and not re.search(version_pattern, version_str):
                    continue
                versioned_dafny.append((version_str, path))

    result = sorted(versioned_dafny, key=lambda x: tuple(map(int, x[0].split("."))))
    return [result[-1]] if latest and result else result


def forbid_assume_statements(file_path: Path):
    with open(file_path, 'r', encoding='utf-8') as f:
        lines = f.readlines()

    for i, line in enumerate(lines):
        if re.search(r'(^|\s)assume\s', line) and not re.search(r'//.*assume', line):
            print(f"Error: 'assume' statement found in {file_path} at line {i + 1}:")
            print(f"    {line.strip()}")
            sys.exit(1)


def run_verification(
    dafny_path: Path,
    dafny_version: str,
    dafny_file: Path,
    verify_dependencies: bool,
    verbosity: Optional[int],
    show_output: bool
) -> Tuple[str, str, int, float]:
    verify_cmd = [str(dafny_path), "verify", "--verification-time-limit=300"]
    if verify_dependencies:
        verify_cmd.append("--verify-included-files")
    if verbosity is not None:
        print('--verbosity is currently unsupported')
    verify_cmd.append(str(dafny_file))

    print(f"\nVerifying {dafny_file.name} with Dafny {dafny_version}")
    print("Command:", " ".join(verify_cmd))

    start = time.time()
    try:
        result = subprocess.run(verify_cmd, capture_output=True, text=True)
        if show_output:
            print(result.stdout)
            print(result.stderr, file=sys.stderr)
        exit_code = result.returncode
    except subprocess.CalledProcessError as e:
        print(f"Verification failed: {e}")
        exit_code = e.returncode
    end = time.time()

    duration = end - start
    print(f"Time taken: {duration:.2f} seconds")
    print(f"Exit code: {exit_code}")
    print("-" * 40)

    return (dafny_file.name, dafny_version, exit_code, duration)


def main():
    args = parse_arguments()
    results = []

    dafny_extension_dir = find_dafny_extension_dir()
    if not dafny_extension_dir:
        print("Error: Dafny VSCode extension directory not found in any known locations.")
        sys.exit(1)

    print(f"Using Dafny extension directory: {dafny_extension_dir}")
    resources_dir = dafny_extension_dir / "out/resources"
    dafny_versions = find_dafny_versions(resources_dir, args.latest, args.version)

    if not dafny_versions:
        print(f"Error: No Dafny executables found in {resources_dir}")
        sys.exit(1)

    for file_str in args.dafny_files:
        try:
            dafny_file = Path(file_str).expanduser().resolve(strict=True)
        except FileNotFoundError:
            print(f"Error: Dafny file '{file_str}' not found.")
            continue

        if args.exclude and re.search(args.exclude, str(dafny_file)):
            print(f"Skipping file '{dafny_file}' due to exclude pattern '{args.exclude}'")
            continue

        if args.forbid_assume:
            forbid_assume_statements(dafny_file)

        for dafny_version, dafny_path in dafny_versions:
            result = run_verification(
                dafny_path=dafny_path,
                dafny_version=dafny_version,
                dafny_file=dafny_file,
                verify_dependencies=args.verify_dependencies,
                verbosity=args.verbosity,
                show_output=args.show_dafny_output,
            )
            results.append(result)

    # Summary Report
    print("\n📋 Verification Report")
    print("=" * 60)
    for filename, version, code, duration in results:
        print(f"{filename:<30} | Dafny {version:<8} | Exit {code:<2} | {duration:.2f}s")
    print("=" * 60)


if __name__ == "__main__":
    main()

