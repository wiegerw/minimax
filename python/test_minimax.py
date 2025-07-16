# Copyright 2025 Wieger Wesselink.
# Distributed under the Boost Software License, Version 1.0.
# (See accompanying file LICENSE or http://www.boost.org/LICENSE_1_0.txt)

"""
This example checks the result of various minimax and negamax algorithms on random game trees.
Moreover, it contains a test for the NegamaxTTM counter example.
"""

import random
from typing import Optional, Tuple, Dict

from game_trees import make_random_game_tree, tree_depth, truncate_at_depth, Node, Color, \
    collect_nodes, draw_tree
from minimax import minimax_tt, minimax_classic, minimax_ab_knuth_1975, minimax_ab_depth_wiki_2025, \
    minimax_ab_fishburn_1983, minimax_ab_wiki_2025
from negamax import negamax_ttw, negamax_ab_fishburn_1983, \
    negamax_ab_wiki_2025, negamax_ab_knuth_1975, negamax_ttm, \
    negamax_classic, negamax_ttw_marsland_lookup, negamax_ttw_fishburn_propagation, \
    negamax_ttw_current_alpha, negamax_ab_pvs_wiki_2025
from definitions import TranspositionTable, minimax, is_minimax_ab_result, is_negamax_ab_result, negamax, \
    is_negamax_tt_result, is_minimax_tt_result


def print_header():
    """Print a formatted header for the test results."""
    print("=" * 80)
    print(f"{'Algorithm Name':<40} | {'Value':>6} | {'Status'}")
    print("=" * 80)


def print_separator():
    """Print a separator line between test cases."""
    print("-" * 80)


def check_result(name: str, value: int, passed: Optional[bool]) -> None:
    print(f"{name:<40} | {value:>6} | {passed}")
    if not passed:
        raise RuntimeError("The test case failed.")


def test_minimax_algorithms(N=10, node_count=6, bound=5):
    """
    Test various minimax and negamax algorithms on random game trees.
    
    Args:
        N: Number of random trees to generate
        node_count: Number of nodes in each random tree
        bound: Bound for random evaluation values
    """

    for i in range(N):
        u = make_random_game_tree(node_count, bound)
        max_depth = tree_depth(u)

        # Use varying alpha, beta, and depth values
        alpha = random.randint(-bound, bound-1)
        beta = random.randint(alpha+1, bound)
        depth = random.randint(1, max(1, max_depth))

        value = minimax_classic(u)
        passed = value == minimax(u)
        check_result('minimax_classic', value, passed)

        value = minimax_ab_knuth_1975(u, alpha, beta)
        passed = is_minimax_ab_result(value, u, alpha, beta)
        check_result('minimax_ab_knuth_1975', value, passed)

        value = minimax_ab_fishburn_1983(u, alpha, beta)
        passed = is_minimax_ab_result(value, u, alpha, beta)
        check_result('minimax_ab_fishburn_1983', value, passed)

        value = minimax_ab_wiki_2025(u, alpha, beta)
        passed = is_minimax_ab_result(value, u, alpha, beta)
        check_result('minimax_ab_wiki_2025', value, passed)

        value = minimax_ab_depth_wiki_2025(u, alpha, beta, depth)
        passed = is_minimax_ab_result(value, truncate_at_depth(u, depth), alpha, beta)
        check_result('minimax_ab_depth_wiki_2025', value, passed)

        value = minimax_tt(u, alpha, beta, depth, T=TranspositionTable())
        passed = is_minimax_tt_result(value, u, alpha, beta, depth)
        check_result('minimax_tt', value, passed)

        value = negamax_classic(u)
        passed = value == negamax(u)
        check_result('negamax_classic', value, passed)

        value = negamax_ab_knuth_1975(u, alpha, beta)
        passed = is_negamax_ab_result(value, u, alpha, beta)
        check_result('negamax_ab_knuth_1975', value, passed)

        value = negamax_ab_fishburn_1983(u, alpha, beta)
        passed = is_negamax_ab_result(value, u, alpha, beta)
        check_result('negamax_ab_fishburn_1983', value, passed)

        value = negamax_ab_wiki_2025(u, alpha, beta)
        passed = is_negamax_ab_result(value, u, alpha, beta)
        check_result('negamax_ab_wiki_2025', value, passed)

        value = negamax_ab_pvs_wiki_2025(u, alpha, beta)
        passed = is_negamax_ab_result(value, u, alpha, beta)
        check_result('negamax_ab_pvs_wiki_2025', value, passed)

        value = negamax_ttm(u, alpha, beta, depth, T=TranspositionTable())
        passed = True  # No correctness criterion available
        check_result('negamax_ttm', value, passed)

        value = negamax_ttw(u, alpha, beta, depth, T=TranspositionTable())
        passed = is_negamax_tt_result(value, u, alpha, beta, depth)
        check_result('negamax_ttw', value, passed)

        value = negamax_ttw_marsland_lookup(u, alpha, beta, depth, T=TranspositionTable())
        passed = is_negamax_tt_result(value, u, alpha, beta, depth)
        check_result('negamax_ttw_marsland_lookup', value, passed)

        value = negamax_ttw_current_alpha(u, alpha, beta, depth, T=TranspositionTable())
        passed = is_negamax_tt_result(value, u, alpha, beta, depth)
        check_result('negamax_ttw_current_alpha', value, passed)

        value = negamax_ttw_fishburn_propagation(u, alpha, beta, depth, T=TranspositionTable())
        passed = is_negamax_tt_result(value, u, alpha, beta, depth)
        check_result('negamax_ttw_fishburn_propagation', value, passed)

        # Optionally draw the tree (uncomment for debugging)
        # draw_tree(u, f"tree_{i}")
    

def check_marsland_counter_example():

    def make_tree() -> Tuple[Node, Dict[str, Node]]:
        d = Node(id='d', color=Color.Black, eval=3, children=[])
        f = Node(id='f', color=Color.White, eval=2, children=[])
        g = Node(id='g', color=Color.White, eval=1, children=[])
        h = Node(id='h', color=Color.Black, eval=4, children=[])
        c = Node(id='c', color=Color.White, eval=0, children=[d, h])
        b = Node(id='b', color=Color.Black, eval=0, children=[c])
        e = Node(id='e', color=Color.Black, eval=0, children=[f, g])
        v = Node(id='v', color=Color.White, eval=0, children=[b, e])
        q = Node(id='q', color=Color.White, eval=1, children=[])
        z = Node(id='z', color=Color.White, eval=2, children=[])
        y = Node(id='y', color=Color.Black, eval=0, children=[z, v, q])
        m = Node(id='m', color=Color.Black, eval=0, children=[v])
        l = Node(id='l', color=Color.White, eval=0, children=[m])
        k = Node(id='k', color=Color.Black, eval=0, children=[l])
        u = Node(id='u', color=Color.White, eval=0, children=[y, k])
        node_map = {x.id: x for x in collect_nodes(u)}
        return u, node_map

    u, node_map = make_tree()
    alpha = 0
    beta = 5
    depth = 6
    value = negamax_ttm(u, alpha, beta, depth, T=TranspositionTable())
    passed = is_negamax_tt_result(value, u, alpha, beta, depth)
    check_result('negamax_ttm', value, passed)


if __name__ == '__main__':
    # Check that the minimax and negamax implementations satisfy their postcondition.
    test_minimax_algorithms(N=10000, node_count=8, bound=3)

    # Verify that the result of the counterexample does not satisfy the predicate `is_negamax_tt_result`.
    print('--- Checking the counter example for NegamaxTTM ---')
    check_marsland_counter_example()

