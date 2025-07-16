# Copyright 2025 Wieger Wesselink.
# Distributed under the Boost Software License, Version 1.0.
# (See accompanying file LICENSE or http://www.boost.org/LICENSE_1_0.txt)

"""
This module contains core definitions and functions for the minimax algorithm and its variants.
It provides implementations of minimax, negamax, and related utility functions for game tree evaluation.
"""

from enum import Enum
from typing import Iterable

from game_trees import Node, all_or_none_extensions
from utilities import MinimaxSettings


def implies(P: bool, Q: bool) -> bool:
    """
    Implements logical implication: P implies Q is equivalent to (not P) or Q.
    
    Args:
        P: The antecedent (premise) of the implication
        Q: The consequent (conclusion) of the implication
        
    Returns:
        bool: True if the implication holds, False otherwise
    """
    return (not P) or Q


def minimum(x: Iterable[int]) -> int:
    """
    Finds the minimum value in an iterable of integers.
    Returns INFINITY if the iterable is empty.
    
    Args:
        x: An iterable of integers
        
    Returns:
        int: The minimum value or INFINITY if empty
    """
    x_ = list(x)
    if len(x_) == 0:
        return MinimaxSettings.INFINITY
    else:
        return min(x_)


def maximum(x: Iterable[int]) -> int:
    """
    Finds the maximum value in an iterable of integers.
    Returns -INFINITY if the iterable is empty.
    
    Args:
        x: An iterable of integers
        
    Returns:
        int: The maximum value or -INFINITY if empty
    """
    x_ = list(x)
    if len(x_) == 0:
        return -MinimaxSettings.INFINITY
    else:
        return max(x_)


def minimax(u: Node) -> int:
    """
    Implements the classic minimax algorithm for game tree evaluation.
    
    Args:
        u: The root node of the game tree
        
    Returns:
        int: The minimax value of the node
    """
    if len(u.children) == 0:
        return u.eval
    if u.color.value == -1:
        return minimum(minimax(v) for v in u.children)
    else:  # u.color.value == 1:
        return maximum(minimax(v) for v in u.children)


def negamax(u: Node) -> int:
    """
    Implements the negamax algorithm, which is a variant of minimax that
    simplifies the implementation by using the fact that max(a,b) = -min(-a,-b).
    
    Args:
        u: The root node of the game tree
        
    Returns:
        int: The negamax value of the node
    """
    if len(u.children) == 0:
        return u.color.value * u.eval
    return maximum(-negamax(v) for v in u.children)


def partial_negamax(u: Node, i: int) -> int:
    """
    Computes the negamax value considering only the first i children of node u.
    
    Args:
        u: The root node of the game tree
        i: The number of children to consider
        
    Returns:
        int: The partial negamax value
    """
    return maximum(-negamax(v) for v in u.children[:i])


def is_ab_result(value: int, x: int, alpha: int, beta: int) -> bool:
    """
    Checks if a value is equivalent to x under alpha-beta pruning constraints.
    
    Args:
        value: The value to check
        x: The reference value
        alpha: The alpha bound
        beta: The beta bound
        
    Returns:
        bool: True if the value is alpha-beta equivalent to x, False otherwise
    """
    a = implies(value <= alpha, x <= value)
    b = implies(alpha < value < beta, x == value)
    c = implies(value >= beta, x >= value)
    return a and b and c


def is_partial_negamax_result(value: int, u: Node, i: int, alpha: int, beta: int) -> bool:
    """
    Checks if a value is equivalent to the partial negamax value under alpha-beta pruning.
    
    Args:
        value: The value to check
        u: The root node of the game tree
        i: The number of children to consider
        alpha: The alpha bound
        beta: The beta bound
        
    Returns:
        bool: True if the value is equivalent to the partial negamax value, False otherwise
    """
    return is_ab_result(value, partial_negamax(u, i), alpha, beta)


def is_minimax_ab_result(value: int, u: Node, alpha: int, beta: int) -> bool:
    """
    Checks if a value is equivalent to the minimax value under alpha-beta pruning.

    Args:
        value: The value to check
        u: The root node of the game tree
        alpha: The alpha bound
        beta: The beta bound

    Returns:
        bool: True if the value is equivalent to the minimax value, False otherwise
    """
    return is_ab_result(value, minimax(u), alpha, beta)


def is_negamax_ab_result(value: int, u: Node, alpha: int, beta: int) -> bool:
    """
    Checks if a value is equivalent to the negamax value under alpha-beta pruning.
    
    Args:
        value: The value to check
        u: The root node of the game tree
        alpha: The alpha bound
        beta: The beta bound
        
    Returns:
        bool: True if the value is equivalent to the negamax value, False otherwise
    """
    return is_ab_result(value, negamax(u), alpha, beta)


def is_minimax_tt_result(value: int, u: Node, alpha: int, beta: int, depth: int) -> bool:
    """
    Checks if a value is equivalent to the negamax value of an all-or-nomn extension of
    truncate_at_depth(u, depth).

    N.B. This predicate should only be applied to very small game trees.

    Args:
        value: The value to check
        u: The root node of the game tree
        alpha: The alpha bound
        beta: The beta bound
        depth: The remaining search depth

    Returns:
        bool: True if the value is equivalent to a minimax value of an extension, False otherwise
    """
    extensions = all_or_none_extensions(u, depth)
    return any(is_minimax_ab_result(value, u1, alpha, beta) for u1 in extensions)


def is_negamax_tt_result(value: int, u: Node, alpha: int, beta: int, depth: int) -> bool:
    """
    Checks if a value is equivalent to the negamax value of an all-or-none extension of
    truncate_at_depth(u, depth).

    N.B. This predicate should only be applied to very small game trees.

    Args:
        value: The value to check
        u: The root node of the game tree
        alpha: The alpha bound
        beta: The beta bound
        depth: The remaining search depth

    Returns:
        bool: True if the value is equivalent to a negamax value of an extension, False otherwise
    """
    extensions = all_or_none_extensions(u, depth)
    return any(is_negamax_ab_result(value, u1, alpha, beta) for u1 in extensions)


class TableFlag(Enum):
    """
    Enumeration of flags used in transposition table entries.
    
    Attributes:
        Exact: The stored value is exact
        Lowerbound: The stored value is a lower bound
        Upperbound: The stored value is an upper bound
    """
    Exact = 0
    Lowerbound = 1
    Upperbound = 2

    def __str__(self):
        return self.name.lower()


class TableEntry(object):
    """
    Represents an entry in a transposition table.
    
    Attributes:
        value: The evaluation value
        depth: The depth at which this value was computed
        flag: The type of value (exact, lowerbound, or upperbound)
    """
    def __init__(self, value: int, depth: int, flag: TableFlag) -> None:
        """
        Initialize a transposition table entry.
        
        Args:
            value: The evaluation value
            depth: The depth at which this value was computed
            flag: The type of value (exact, lowerbound, or upperbound)
        """
        self.value = value
        self.depth = depth
        self.flag = flag


    def __repr__(self) -> str:
        return f"({self.value},{self.depth},{str(self.flag)})"


class TranspositionTable(dict):
    def __repr__(self) -> str:
        items = (f"{key}:{repr(value)}" for key, value in self.items())
        return "{" + ", ".join(items) + "}"


def print_table(T: TranspositionTable) -> None:
    """
    Prints the contents of a transposition table.
    
    Args:
        T: The transposition table to print
    """
    print('--- transposition table ---')
    for id in T:
        t = T[id]
        print(f'id={id:2} value={t.value:2} depth={t.depth:2} flag={t.flag}')
