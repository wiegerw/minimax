# Copyright 2025 Wieger Wesselink.
# Distributed under the Boost Software License, Version 1.0.
# (See accompanying file LICENSE or http://www.boost.org/LICENSE_1_0.txt)

"""
This module provides various implementations of the minimax algorithm with alpha-beta pruning.

The minimax algorithm is a decision rule used in artificial intelligence and game theory for
minimizing the possible loss in a worst-case scenario. When dealing with games, it's used to
find the optimal move for a player, assuming that the opponent is also playing optimally.

This module includes several implementations:
- Basic minimax without pruning
- Alpha-beta pruning variants
- Transposition table enhanced versions
- Depth-limited search

Each implementation follows the same basic pattern but with different optimizations.
"""

from logger import log
from definitions import TranspositionTable, TableFlag, TableEntry
from game_trees import Node, Color
from utilities import MinimaxSettings

def minimax_classic(u: Node) -> int:
    """Standard recursive minimax.
    
    This is a straightforward implementation of the minimax algorithm without
    any pruning or optimizations. It explores the entire game tree to find the
    optimal move.
    
    Args:
        u: The current node in the game tree
        
    Returns:
        int: The minimax value of the node
    """
    if not u.children:
        return u.eval
    if u.color == Color.Black:
        value = MinimaxSettings.INFINITY
        for v in u.children:
            value = min(value, minimax_classic(v))
        return value
    else:  # u.color == Color.White:
        value = -MinimaxSettings.INFINITY
        for v in u.children:
            value = max(value, minimax_classic(v))
        return value


def minimax_ab_knuth_1975(u: Node, alpha: int, beta: int) -> int:
    """
    Implementation of minimax with alpha-beta pruning based on Knuth and Moore's 1975 paper.

    Args:
        u: The current node in the game tree
        alpha: The lower bound of the search window
        beta: The upper bound of the search window

    Returns:
        int: The minimax value of the node
    """
    if not u.children:
        return u.eval
    if u.color == Color.Black:
        value = beta
        for v in u.children:
            value = min(value, minimax_ab_knuth_1975(v, alpha, beta))
            if value <= alpha:
                break
        return value
    else:
        value = alpha
        for v in u.children:
            value = max(value, minimax_ab_knuth_1975(v, alpha, beta))
            if value >= beta:
                break
        return value


def minimax_ab_fishburn_1983(u: Node, alpha: int, beta: int) -> int:
    """
    Implementation of minimax with alpha-beta pruning based on Fishburn's 1983 paper.

    Args:
        u: The current node in the game tree
        alpha: The lower bound of the search window
        beta: The upper bound of the search window

    Returns:
        int: The minimax value of the node
    """
    if not u.children:
        return u.eval
    if u.color == Color.Black:
        value = MinimaxSettings.INFINITY
        for v in u.children:
            value = min(value, minimax_ab_fishburn_1983(v, alpha, min(value, beta)))
            if value <= alpha:
                break
        return value
    else:
        value = -MinimaxSettings.INFINITY
        for v in u.children:
            value = max(value, minimax_ab_fishburn_1983(v, max(value, alpha), beta))
            if value >= beta:
                break
        return value


def minimax_ab_wiki_2025(u: Node, alpha: int, beta: int) -> int:
    """
    Implementation of minimax with alpha-beta pruning based on Wikipedia.

    Args:
        u: The current node in the game tree
        alpha: The lower bound of the search window
        beta: The upper bound of the search window

    Returns:
        int: The minimax value of the node
    """
    if not u.children:
        return u.eval
    if u.color == Color.Black:
        value = MinimaxSettings.INFINITY
        for v in u.children:
            value = min(value, minimax_ab_wiki_2025(v, alpha, beta))
            beta = min(beta, value)
            if alpha >= beta:
                break
        return value
    else:
        value = -MinimaxSettings.INFINITY
        for v in u.children:
            value = max(value, minimax_ab_wiki_2025(v, alpha, beta))
            alpha = max(alpha, value)
            if alpha >= beta:
                break
        return value


def minimax_ab_depth_wiki_2025(u: Node, alpha: int, beta: int, depth: int) -> int:
    """
    Implementation of depth-limited minimax with alpha-beta pruning.
    
    This version limits the search to a specified depth, which is essential for
    games with large branching factors where exploring the entire tree is impractical.
    When the depth limit is reached, the evaluation function is used to estimate
    the value of the position.
    
    Args:
        u: The current node in the game tree
        alpha: The lower bound of the search window
        beta: The upper bound of the search window
        depth: The remaining search depth
        
    Returns:
        int: The minimax value of the node
    """
    # If we've reached a leaf node or the depth limit, return the evaluation
    if depth == 0 or not u.children:
        return u.eval
        
    if u.color == Color.Black:  # Minimizing player
        value = beta
        for v in u.children:
            value = min(value, minimax_ab_depth_wiki_2025(v, alpha, beta, depth - 1))
            beta = min(beta, value)
            if alpha >= beta:
                break  # Alpha cutoff
        return value
    else:  # Maximizing player (White)
        value = alpha
        for v in u.children:
            value = max(value, minimax_ab_depth_wiki_2025(v, alpha, beta, depth - 1))
            alpha = max(alpha, value)
            if alpha >= beta:
                break  # Beta cutoff
        return value


def minimax_tt(u: Node, alpha: int, beta: int, depth: int, T: TranspositionTable) -> int:
    """
    Implementation of minimax with alpha-beta pruning and transposition tables.
    
    This version enhances the depth-limited alpha-beta search with a transposition table
    to avoid re-searching positions that have already been evaluated. This is particularly
    effective in games where the same position can be reached through different move sequences.
    
    The implementation is based on the approach described in "Learning to Play" by Aske Plaat (2020),
    but without the best move handling optimization.
    
    Args:
        u: The current node in the game tree
        alpha: The lower bound of the search window
        beta: The upper bound of the search window
        depth: The remaining search depth
        T: The transposition table for storing evaluated positions
        
    Returns:
        int: The minimax value of the node
    """
    alpha0 = alpha

    if u.id in T:
        t = T[u.id]
        if t.depth >= depth:
            if (t.flag == TableFlag.Exact or
               (t.flag == TableFlag.Lowerbound and t.value >= beta) or
               (t.flag == TableFlag.Upperbound and t.value <= alpha)):
                return t.value

    if depth == 0 or not u.children:
        return u.eval

    if u.color == Color.Black:
        value = beta
        for v in u.children:
            value = min(value, minimax_tt(v, alpha, beta, depth - 1, T))
            beta = min(beta, value)
            if alpha >= beta:
                break
    else:
        value = alpha
        for v in u.children:
            value = max(value, minimax_tt(v, alpha, beta, depth - 1, T))
            alpha = max(alpha, value)
            if alpha >= beta:
                break

    if value <= alpha0:
        flag = TableFlag.Upperbound
    elif value >= beta:
        flag = TableFlag.Lowerbound
    else:
        flag = TableFlag.Exact
    T[u.id] = TableEntry(value, depth, flag)

    log(f'minimax_tt({u.id}, alpha={alpha0}, beta={beta}, depth={depth}) -> value={value}, flag={flag}')
    return value


