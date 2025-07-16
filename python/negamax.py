# Copyright 2025 Wieger Wesselink.
# Distributed under the Boost Software License, Version 1.0.
# (See accompanying file LICENSE or http://www.boost.org/LICENSE_1_0.txt)

"""
This module provides various implementations of the negamax algorithm with alpha-beta pruning.

The negamax algorithm is a variant of minimax that simplifies the implementation by using
the fact that max(a,b) = -min(-a,-b). This module includes several implementations from
different sources, as well as versions that use transposition tables for improved performance.
"""

from logger import log
from definitions import TranspositionTable, TableFlag, TableEntry
from game_trees import Node
from utilities import MinimaxSettings


def negamax_classic(u: Node) -> int:
    """Negamax classic.

    Args:
        u: The current node in the game tree

    Returns:
        int: The negamax value of the node
    """
    if not u.children:
        return u.color.value * u.eval
    value = -MinimaxSettings.INFINITY
    for v in u.children:
        value = max(value, -negamax_classic(v))
    return value


def negamax_depth(u: Node, depth: int) -> int:
    """Depth-limited negamax.

    Args:
        u: The current node in the game tree
        depth: The remaining search depth

    Returns:
        int: The negamax value of the node
    """
    if depth == 0 or not u.children:
        return u.color.value * u.eval
    value = -MinimaxSettings.INFINITY
    for v in u.children:
        value = max(value, -negamax_depth(v, depth - 1))
    return value


def negamax_ab_knuth_1975(u: Node, alpha: int, beta: int) -> int:
    """Negamax with alpha-beta pruning (Knuth & Moore, 1975).

    Args:
        u: The current node in the game tree
        alpha: The lower bound of the search window
        beta: The upper bound of the search window
        
    Returns:
        int: The negamax value of the node
    """
    if not u.children:
        return u.color.value * u.eval
    value = alpha
    for v in u.children:
        value = max(value, -negamax_ab_knuth_1975(v, -beta, -value))
        if value >= beta:
            return beta
    return value


def negamax_ab_fishburn_1983(u: Node, alpha: int, beta: int) -> int:
    """Negamax with alpha-beta pruning (Fishburn, 1983).

    Args:
        u: The current node in the game tree
        alpha: The lower bound of the search window
        beta: The upper bound of the search window
        
    Returns:
        int: The negamax value of the node
    """
    if not u.children:
        return u.color.value * u.eval
    value = -MinimaxSettings.INFINITY
    for v in u.children:
        value = max(value, -negamax_ab_fishburn_1983(v, -beta, -max(value, alpha)))
        if value >= beta:
            break
    return value


def negamax_ab_wiki_2025(u: Node, alpha: int, beta: int) -> int:
    """
    Implementation of negamax with alpha-beta pruning based on the Wikipedia formulation.
    
    Args:
        u: The current node in the game tree
        alpha: The lower bound of the search window
        beta: The upper bound of the search window
        
    Returns:
        int: The negamax value of the node
    """
    if not u.children:
        return u.color.value * u.eval
    else:
        value = -MinimaxSettings.INFINITY
        for v in u.children:
            value = max(value, -negamax_ab_wiki_2025(v, -beta, -alpha))
            alpha = max(alpha, value)
            if alpha >= beta:
                break
    return value


def negamax_ab_pvs_wiki_2025(u: Node, alpha: int, beta: int) -> int:
    """
    Implementation of negamax with alpha-beta pruning and PVS based on the Wikipedia formulation.

    Args:
        u: The current node in the game tree
        alpha: The lower bound of the search window
        beta: The upper bound of the search window

    Returns:
        int: The negamax value of the node
    """
    if not u.children:
        return u.color.value * u.eval
    else:
        value = -MinimaxSettings.INFINITY
        for i, v in enumerate(u.children):
            if i == 0:
                negamax_v = negamax_ab_pvs_wiki_2025(v, -beta, -alpha)
            else:
                negamax_v = negamax_ab_pvs_wiki_2025(v, -alpha - 1, -alpha)
                if alpha < -negamax_v < beta:
                    negamax_v = negamax_ab_pvs_wiki_2025(v, -beta, -alpha)
            value = max(value, -negamax_v)
            alpha = max(alpha, value)
            if alpha >= beta:
                break
    return value


def negamax_ttm(u: Node, alpha: int, beta: int, depth: int, T: TranspositionTable) -> int:
    """
    This is the Marsland 1986 version of negamax with a transposition table.

    Args:
        u: The current node in the game tree
        alpha: The lower bound of the search window
        beta: The upper bound of the search window
        depth: The remaining search depth
        T: The transposition table for storing evaluated positions

    Returns:
        int: The negamax value of the node
    """
    alpha0 = alpha

    # Retrieve from transposition table
    if u.id in T:
        t = T[u.id]
        if t.depth >= depth:
            if t.flag == TableFlag.Exact:
                return t.value
            elif t.flag == TableFlag.Lowerbound:
                alpha = max(alpha, t.value)
            elif t.flag == TableFlag.Upperbound:
                beta = min(beta, t.value)
            if alpha >= beta:
                return t.value

    # Terminal node or depth limit reached
    if depth == 0 or not u.children:
        return u.color.value * u.eval

    # The Fishburn 1983 variant of alpha-beta
    value = -MinimaxSettings.INFINITY
    for v in u.children:
        value = max(value, -negamax_ttm(v, -beta, -max(value, alpha), depth - 1, T))
        if value >= beta:
            break

    # Determine flag for storing in table (compare with alpha instead of alpha0!)
    flag = TableFlag.Exact
    if value <= alpha:
        flag = TableFlag.Upperbound
    if value >= beta:
        flag = TableFlag.Lowerbound

    # A constraint on the depth
    if u.id not in T or T[u.id].depth <= depth:
        T[u.id] = TableEntry(value, depth, flag)

    log(f'negamax_ttm({u.id}, alpha={alpha0}, beta={beta}, depth={depth}) -> value={value}, flag={flag}')
    return value


def negamax_ttw(u: Node, alpha: int, beta: int, depth: int, T: TranspositionTable) -> int:
    """
    An implementation of depth-limited negamax with alpha-beta pruning and transposition tables.

    This is the Wikipedia version.

    Args:
        u: The current node in the game tree
        alpha: The lower bound of the search window
        beta: The upper bound of the search window
        depth: The remaining search depth
        T: The transposition table for storing evaluated positions

    Returns:
        int: The negamax value of the node
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
        return u.color.value * u.eval
    value = -MinimaxSettings.INFINITY
    for v in u.children:
        value = max(value, -negamax_ttw(v, -beta, -alpha, depth - 1, T))
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

    log(f'negamax_ttw({u.id}, alpha={alpha0}, beta={beta}, depth={depth}) -> value={value}, flag={flag}')
    return value


def negamax_ttw_marsland_lookup(u: Node, alpha: int, beta: int, depth: int, T: TranspositionTable) -> int:
    """
    This is a modified version of negamax_ttw, in which the Marsland 1986 transposition table lookup scheme
    is used.

    Args:
        u: The current node in the game tree
        alpha: The lower bound of the search window
        beta: The upper bound of the search window
        depth: The remaining search depth
        T: The transposition table for storing evaluated positions

    Returns:
        int: The negamax value of the node
    """
    alpha0 = alpha

    # Retrieve from transposition table
    if u.id in T:
        t = T[u.id]
        if t.depth >= depth:
            if t.flag == TableFlag.Exact:
                return t.value
            elif t.flag == TableFlag.Lowerbound:
                alpha = max(alpha, t.value)
            elif t.flag == TableFlag.Upperbound:
                beta = min(beta, t.value)
            if alpha >= beta:
                return t.value

    # Terminal node or depth limit reached
    if depth == 0 or not u.children:
        return u.color.value * u.eval

    value = -MinimaxSettings.INFINITY
    for v in u.children:
        value = max(value, -negamax_ttw_marsland_lookup(v, -beta, -max(value, alpha), depth - 1, T))
        if value >= beta:
            break

    # Determine flag for storing in table
    if value <= alpha0:
        flag = TableFlag.Upperbound
    elif value >= beta:
        flag = TableFlag.Lowerbound
    else:
        flag = TableFlag.Exact

    log(f'negamax_ttw_marsland_lookup({u.id}, alpha={alpha0}, beta={beta}, depth={depth}) -> value={value}, flag={flag}')
    return value


def negamax_ttw_fishburn_propagation(u: Node, alpha: int, beta: int, depth: int, T: TranspositionTable) -> int:
    """
    This is a modified version of negamax_ttw, in which the value propagation scheme of Fishburn 1983 is used.

    Args:
        u: The current node in the game tree
        alpha: The lower bound of the search window
        beta: The upper bound of the search window
        depth: The remaining search depth
        T: The transposition table for storing evaluated positions

    Returns:
        int: The negamax value of the node
    """
    alpha0 = alpha

    if u.id in T:
        t = T[u.id]
        if t.depth >= depth:
            if t.flag == TableFlag.Exact:
                return t.value
            elif t.flag == TableFlag.Lowerbound:
                alpha = max(alpha, t.value)
            elif t.flag == TableFlag.Upperbound:
                beta = min(beta, t.value)
        if alpha >= beta:
            return t.value

    if depth == 0 or not u.children:
        return u.color.value * u.eval
    value = -MinimaxSettings.INFINITY
    for v in u.children:
        value = max(value, -negamax_ttw_fishburn_propagation(v, -beta, -max(value, alpha), depth - 1, T))
        if value >= beta:
            break

    if value <= alpha0:
        flag = TableFlag.Upperbound
    elif value >= beta:
        flag = TableFlag.Lowerbound
    else:
        flag = TableFlag.Exact
    T[u.id] = TableEntry(value, depth, flag)

    log(f'negamax_ttw_fishburn_update({u.id}, alpha={alpha}, beta={beta}, depth={depth}) -> value={value}, flag={flag}')
    return value


def negamax_ttw_current_alpha(u: Node, alpha: int, beta: int, depth: int, T: TranspositionTable) -> int:
    """
    This is a modified version of negamax_ttw, in which the transposition table is updated based on the
    current value of alpha.

    Args:
        u: The current node in the game tree
        alpha: The lower bound of the search window
        beta: The upper bound of the search window
        depth: The remaining search depth
        T: The transposition table for storing evaluated positions

    Returns:
        int: The negamax value of the node
    """
    if u.id in T:
        t = T[u.id]
        if t.depth >= depth:
            if t.flag == TableFlag.Exact:
                return t.value
            elif t.flag == TableFlag.Lowerbound:
                alpha = max(alpha, t.value)
            elif t.flag == TableFlag.Upperbound:
                beta = min(beta, t.value)
        if alpha >= beta:
            return t.value

    if depth == 0 or not u.children:
        return u.color.value * u.eval
    value = -MinimaxSettings.INFINITY
    for v in u.children:
        value = max(value, -negamax_ttw_current_alpha(v, -beta, -alpha, depth - 1, T))
        alpha = max(alpha, value)
        if alpha >= beta:
            break

    if value <= alpha:
        flag = TableFlag.Upperbound
    elif value >= beta:
        flag = TableFlag.Lowerbound
    else:
        flag = TableFlag.Exact
    T[u.id] = TableEntry(value, depth, flag)

    log(f'negamax_ttw_current_alpha({u.id}, alpha={alpha}, beta={beta}, depth={depth}) -> value={value}, flag={flag}')
    return value
