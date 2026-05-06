# Copyright 2026 Wieger Wesselink
# Distributed under the Boost Software License, Version 1.0.
# (See accompanying file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)

"""
This module implements the depth-limited MT-SSS* / negamax-Plaat algorithm.
"""

from logger import log
from game_trees import Node, Color
from utilities import MinimaxSettings


class TableEntry(object):
    """
    Represents an entry in the transposition table for the Plaat 1996 algorithm.
    """
    def __init__(self, lowerbound: int = -MinimaxSettings.INFINITY, upperbound: int = MinimaxSettings.INFINITY, depth: int = 0) -> None:
        self.lowerbound = lowerbound
        self.upperbound = upperbound
        self.depth = depth


TranspositionTable = dict[Node, TableEntry]


def negamax_depth_tt_plaat_1996(u: Node, alpha: int, beta: int, depth: int, T: TranspositionTable) -> int:
    """
    Implementation of the depth-limited MT-SSS* / negamax version of Plaat et al. 1996.
    """
    alpha0 = alpha
    beta0 = beta

    # Check if position is in the transposition table
    if u.id in T:
        t = T[u.id]
        if t.depth >= depth:
            if t.lowerbound >= beta:
                return t.lowerbound
            if t.upperbound <= alpha:
                return t.upperbound

    if depth == 0 or not u.children:
        return u.color.value * u.eval

    value = -MinimaxSettings.INFINITY
    for v in u.children:
        value = max(value, -negamax_depth_tt_plaat_1996(v, -beta, -alpha, depth - 1, T))
        alpha = max(alpha, value)
        if alpha >= beta:
            break

    lower = -MinimaxSettings.INFINITY
    upper = MinimaxSettings.INFINITY
    if value < beta0:
        upper = value
    if value > alpha0:
        lower = value
    T[u.id] = TableEntry(lowerbound=lower, upperbound=upper, depth=depth)

    log(f'negamax_depth_table_plaat_1996({u.id}, alpha={alpha}, beta={beta}, depth={depth}) -> value={value}')
    return value
