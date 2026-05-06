# Copyright 2025 - 2026 Wieger Wesselink
# Distributed under the Boost Software License, Version 1.0.
# (See accompanying file LICENSE or http://www.boost.org/LICENSE_1_0.txt)

"""
This module implements the MT-SSS* / negamax-Plaat algorithm.
"""

from logger import log
from game_trees import Node, Color
from utilities import MinimaxSettings


class TableEntry(object):
    """
    Represents an entry in the transposition table for the Plaat 1996 algorithm.
    """
    def __init__(self, lowerbound: int = -MinimaxSettings.INFINITY, upperbound: int = MinimaxSettings.INFINITY) -> None:
        self.lowerbound = lowerbound
        self.upperbound = upperbound


TranspositionTable = dict[Node, TableEntry]


def negamax_tt_plaat_1996(u: Node, alpha: int, beta: int, T: TranspositionTable) -> int:
    """
    Implementation of the MT-SSS* / negamax version of Plaat et al. 1996.
    """
    alpha0 = alpha
    beta0 = beta

    # Check if position is in the transposition table
    if u.id in T:
        t = T[u.id]
        if t.lowerbound >= beta:
            return t.lowerbound
        if t.upperbound <= alpha:
            return t.upperbound
    else:
        t = TableEntry()
        T[u.id] = t

    if not u.children:
        return (1 if u.color == Color.White else -1) * u.eval

    value = -MinimaxSettings.INFINITY
    for v in u.children:
        value = max(value, -negamax_tt_plaat_1996(v, -beta, -alpha, T))
        alpha = max(alpha, value)
        if alpha >= beta:
            break

    if value < beta0:
        t.upperbound = value
    if value > alpha0:
        t.lowerbound = value

    log(f'negamax_table_plaat_1996({u.id}, alpha={alpha}, beta={beta}) -> value={value}')
    return value
