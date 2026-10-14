# Verified Minimax and Negamax Search in Dafny

This repository contains the research artifact for a formal verification study of game-tree search algorithms. The work was presented at the [Dafny 2026 Workshop](https://popl26.sigplan.org/home/dafny-2026) and accepted for the [VSTTE 2026 Workshop](https://fmcad.org/FMCAD26/vstte/). The VSTTE submission is available as a [PDF preprint](https://fmcad.org/FMCAD26/vstte/preprints/paper-10.pdf). An extended version is also available on [arXiv](https://arxiv.org/abs/2509.20138).

The study develops a **witness-based correctness criterion** for depth-limited search with transposition tables and uses Dafny to verify a family of minimax and negamax algorithms against it. Corresponding Python implementations support experimentation and randomized testing.

## Repository contents

| Path | Purpose |
| --- | --- |
| `dafny-4.10/` | Dafny source snapshot verified with Dafny 4.10.0. |
| `dafny-4.11/` | Dafny source snapshot verified with Dafny 4.11.0; includes small compatibility adjustments described below. |
| `python/` | Executable minimax and negamax implementations, game-tree utilities, and randomized tests. |
| `logs/` | Captured verification output and per-file verification statistics for both Dafny versions. |
| `scripts/` | Helper scripts, including the Dafny verification runner. |

### Dafny sources

Both versioned Dafny directories contain the shared definitions and lemmas, minimax and negamax implementations, alpha-beta variants, and transposition-table variants. The principal source files are:

| File | Contents |
| --- | --- |
| `definitions.dfy`, `lemmas.dfy` | Shared definitions, correctness predicates, and proof lemmas. |
| `minimax.dfy`, `minimax-alpha-beta.dfy` | Minimax and alpha-beta minimax algorithms. |
| `negamax.dfy`, `negamax-alpha-beta.dfy` | Negamax and alpha-beta negamax algorithms. |
| `negamax-ttp.dfy` | Depth-limited negamax search with a transposition table, based on Plaat, A., Schaeffer, J., Pijls, W., and de Bruin, A., “Best-first fixed-depth minimax algorithms,” *Artificial Intelligence* 87(1–2), 255–293 (1996). Verified using the witness-based correctness criterion. |
| `negamax-ttw.dfy`, `negamax-ttw-variants.dfy` | Depth-limited negamax search with a transposition table, based on the algorithm described in [Wikipedia's Negamax article](https://en.wikipedia.org/wiki/Negamax). Verified using the witness-based correctness criterion. |
| `test-definitions.dfy` | Additional definitions used for verification and testing. |

### Python implementations

The `python/` directory provides executable versions of the algorithms and supporting utilities. In particular, `minimax.py` and `negamax.py` contain the search variants, `definitions.py` contains common definitions and correctness predicates, `game_trees.py` provides game-tree utilities, and `test_minimax.py` exercises the implementations on randomized trees.

## Verification

The Dafny sources were verified with **Dafny 4.10.0** and **Dafny 4.11.0**. For 4.11, small source adjustments were needed to work around internal errors in the verification tool; the adjusted sources are kept separately in `dafny-4.11/`.

### Reproducing the verification

To reproduce the verification reports, install the Dafny VS Code extension with Dafny 4.10.0 and 4.11.0 available, ensure Python 3 is installed, then run these commands from the repository root:

Individual files can also be verified directly with `dafny verify <file.dfy>` (using the desired Dafny version), or by opening them in VS Code with the Dafny extension and running verification there. The commands below batch the verification of all files and save the output to logs.

```sh
scripts/run-dafny.py --version "4.10" dafny-4.10/*.dfy >& logs/dafny-4.10.log
scripts/run-dafny.py --version "4.11" dafny-4.11/*.dfy >& logs/dafny-4.11.log
```

The commands verify every `.dfy` file in the corresponding versioned directory and capture the verifier output in its log. The helper in `scripts/run-dafny.py` locates the Dafny executables supplied by the VS Code extension. Running the commands again replaces the corresponding log files.

The table summarizes the reports at the ends of [`logs/dafny-4.10.log`](logs/dafny-4.10.log) and [`logs/dafny-4.11.log`](logs/dafny-4.11.log). Each listed file completed with exit code 0 in both runs. Times are the elapsed times recorded by those runs and may vary across machines.

| Dafny source | 4.10.0 result | Time (s) | 4.11.0 result | Time (s) |
| --- | ---: | ---: | ---: | ---: |
| `definitions.dfy` | Pass | 0.87 | Pass | 0.86 |
| `lemmas.dfy` | Pass | 1.91 | Pass | 1.50 |
| `minimax-alpha-beta.dfy` | Pass | 3.68 | Pass | 2.41 |
| `minimax.dfy` | Pass | 0.81 | Pass | 0.81 |
| `negamax-alpha-beta.dfy` | Pass | 4.98 | Pass | 4.71 |
| `negamax.dfy` | Pass | 0.86 | Pass | 0.85 |
| `negamax-ttp.dfy` | Pass | 5.63 | Pass | 8.04 |
| `negamax-ttw.dfy` | Pass | 2.11 | Pass | 2.93 |
| `negamax-ttw-variants.dfy` | Pass | 2.17 | Pass | 2.27 |
| `test-definitions.dfy` | Pass | 0.90 | Pass | 0.87 |
| **Total files passing** | **10 / 10** |  | **10 / 10** |  |

## Project status

This repository is intended to serve as a stable artifact accompanying the published work. Further minimax verification work is expected to continue as a separate, larger-scale verification effort.

## License

The software and accompanying materials are distributed under the [Boost Software License 1.0](LICENSE).
