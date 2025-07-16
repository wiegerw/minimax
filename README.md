# Formal Verification of Minimax Algorithms

This repository accompanies our submission to **ACG 2025**, presenting a formal verification study of game tree search algorithms using Dafny. We introduce a **witness-based correctness criterion** for depth-limited search with transposition tables, and verify a representative set of minimax and negamax variants against it. In addition, we provide corresponding Python implementations for experimentation and testing.

## Contents

### `dafny/`
Contains formally verified Dafny implementations of minimax and negamax algorithms, including depth-limited and transposition-table-enhanced variants. These are verified using Dafny 4.10.0.

Key files and classes:

- `minimax.dfy`: `Minimax`
- `minimax-alpha-beta.dfy`:  
  - `MinimaxABKnuth1975Algorithm`  
  - `MinimaxFishburn1983Algorithm`  
  - `MinimaxABWiki2025Algorithm`
- `negamax.dfy`: `NegamaxAlgorithm`
- `negamax-alpha-beta.dfy`:  
  - `NegamaxKnuth1975Algorithm`  
  - `NegamaxFishburn1983Algorithm`  
  - `NegamaxABWikipedia2025Algorithm`, `NegamaxWikipedia2025'Algorithm`
- `negamax-depth-limited.dfy`:  
  - `NegamaxDepthLimitedAlgorithm`  
  - `NegamaxAlphaBetaDepthLimitedAlgorithm`  
  - `NegamaxPVSAlgorithm`
- `negamax-ttw.dfy`: `NegamaxTTW`
- `negamax-ttw-current-alpha.dfy`: `NegamaxTTWCurrentAlpha`
- `negamax-ttw-fishburn-propagation.dfy`: `NegamaxTTWFishburnPropagation`
- `lemmas.dfy`, `definitions.dfy`: Common definitions and supporting lemmas

### `python/`
Provides executable implementations and randomized testing for all verified algorithms. Also includes tools for tree construction, visualization, and correctness checking.

Key files:

- `definitions.py`: Core algorithm definitions and correctness predicates
- `minimax.py`: Classic and alpha-beta minimax variants
- `negamax.py`: Classic, alpha-beta, depth-limited, and transposition table negamax variants
- `minimax_plaat.py`: Plaat-style transposition table version
- `negamax-ttm-counter-example.py`: Counterexample for a Marsland-style variant that violates the witness-based criterion
- `game_trees.py`: Utilities to construct, parse, print, and visualize game trees
- `test_minimax.py`: Randomized testing and correctness checks
- `logger.py`, `utilities.py`: Supporting infrastructure

## Highlights

- ✅ **Witness-based correctness**: A natural and rigorous correctness notion for transposition table search
- ✅ **Formal verification**: Over 15 variants verified in Dafny
- ✅ **Executable Python code**: Validated against randomized game trees
