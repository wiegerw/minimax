# Copyright 2025 Wieger Wesselink.
# Distributed under the Boost Software License, Version 1.0.
# (See accompanying file LICENSE or http://www.boost.org/LICENSE_1_0.txt)

"""
This module implements the MT-SSS* / alphabeta algorithm from the paper
"Best-first Fixed-depth Minimax algorithms" by Plaat et al. (1996).

The algorithm uses a different approach to transposition tables compared to
traditional minimax implementations, storing upper and lower bounds for each position.
"""

from logger import log
from game_trees import Node, Color
from utilities import MinimaxSettings


class TableEntry(object):
    """
    Represents an entry in the transposition table for the Plaat 1996 algorithm.
    
    Unlike traditional transposition table entries that store a single value and a flag,
    this entry stores both upper and lower bounds for a position.
    
    Attributes:
        lowerbound: The lower bound of the position's value
        upperbound: The upper bound of the position's value
    """
    def __init__(self, lowerbound: int = -MinimaxSettings.INFINITY, upperbound: int = MinimaxSettings.INFINITY) -> None:
        """
        Initialize a transposition table entry with bounds.
        
        Args:
            lowerbound: The lower bound of the position's value (default: -INFINITY)
            upperbound: The upper bound of the position's value (default: INFINITY)
        """
        self.lowerbound = lowerbound
        self.upperbound = upperbound


# Type alias for a transposition table, which maps nodes to table entries
TranspositionTable = dict[Node, TableEntry]


def minimax_tt_plaat_1996(u: Node, alpha: int, beta: int, T: TranspositionTable) -> int:
    """
    Implementation of the MT-SSS* / alphabeta algorithm from Plaat et al. 1996.
    
    This algorithm uses a transposition table that stores upper and lower bounds for each position,
    rather than exact values with flags. It's particularly effective for best-first search algorithms
    like SSS* and MTD(f).
    
    Args:
        u: The current node in the game tree
        alpha: The lower bound of the search window
        beta: The upper bound of the search window
        T: The transposition table for storing evaluated positions
        
    Returns:
        int: The minimax value of the node
    """
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
        return u.eval

    if u.color == Color.Black:
        value = MinimaxSettings.INFINITY
        for v in u.children:
            value = min(value, minimax_tt_plaat_1996(v, alpha, beta, T))
            beta = min(beta, value)
    else:
        value = -MinimaxSettings.INFINITY
        for v in u.children:
            value = max(value, minimax_tt_plaat_1996(v, alpha, beta, T))
            alpha = max(alpha, value)

    if value < beta:
        t.upperbound = value
    if value > alpha:
        t.lowerbound = value

    log(f'minimax_table_plaat_1996({u.id}, alpha={alpha}, beta={beta}) -> value={value}')
    return value
