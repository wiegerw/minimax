#!/usr/bin/env python3

# Copyright 2025 Wieger Wesselink.
# Distributed under the Boost Software License, Version 1.0.
# (See accompanying file LICENSE or http://www.boost.org/LICENSE_1_0.txt)

"""
This file is a self-contained implementation of NegamaxTTM + NegamaxTTW.
It also contains the counterexample for the verification of NegamaxTTM using
our correctness criterion for transposition table search.
"""

from enum import Enum
from typing import List, Tuple, Dict
import copy
import graphviz


class Settings:
    INFINITY = 1000
    visited = []


class Color(Enum):
    White = 1
    Black = -1

    def __str__(self):
        return 'White' if self.value == 1 else 'Black'


class Node(object):
    def __init__(self, color: Color, eval: int, children=None, id=None):
        if children is None:
            children = []
        self.color = color
        self.eval = eval
        self.children = children
        self.id = id

    def __repr__(self):
        return str(self.id)

    def __hash__(self):
        return hash(self.id)

    def __eq__(self, other):
        return isinstance(other, Node) and self.id == other.id


class TableFlag(Enum):
    Exact = 0
    Lowerbound = 1
    Upperbound = 2

    def __str__(self):
        if self.value == 0:
            return "EX"
        elif self.value == 1:
            return "LB"
        elif self.value == 2:
            return "UB"


class TableEntry:
    def __init__(self, value: int, depth: int, flag: TableFlag) -> None:
        self.value = value
        self.depth = depth
        self.flag = flag

    def __repr__(self) -> str:
        return f"{self.value}@{self.depth}:{str(self.flag)}"


class TranspositionTable(dict):
    def __repr__(self) -> str:
        items = (f"{key}={repr(value)}" for key, value in self.items())
        return "{" + ", ".join(items) + "}"


# Negamax Wikipedia 2025
def negamax_ttw(u: Node, alpha: int, beta: int, depth: int, T: TranspositionTable) -> int:
    Settings.visited.append(u.id)
    alpha0 = alpha
    T0 = copy.deepcopy(T)

    if u.id in T:
        t = T[u.id]
        if t.depth >= depth:
            if t.flag == TableFlag.Exact:
                return t.value
            elif t.flag == TableFlag.Lowerbound and t.value >= beta:
                return t.value
            elif t.flag == TableFlag.Upperbound and t.value <= alpha:
                return t.value

    if depth == 0 or not u.children:
        return u.color.value * u.eval
    value = -Settings.INFINITY
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

    print(f'negamax_ttw({u.id}, color={u.color}, alpha={alpha0:2}, beta={beta:2}, depth={depth}, T={T0}) = {value:2} ({flag})')
    return value


# Negamax with transposition table (Marsland 1986)
def negamax_ttm(u: Node, alpha: int, beta: int, depth: int, T: TranspositionTable) -> int:
    Settings.visited.append(u.id)
    alpha0 = alpha
    T0 = copy.deepcopy(T)

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

    value = -Settings.INFINITY
    for v in u.children:
        value = max(value, -negamax_ttm(v, -beta, -max(value, alpha), depth - 1, T))
        if value >= beta:
            break

    flag = TableFlag.Exact
    if value <= alpha:
        flag = TableFlag.Upperbound
    if value >= beta:
        flag = TableFlag.Lowerbound
    if u.id not in T or T[u.id].depth <= depth:
        T[u.id] = TableEntry(value, depth, flag)

    print(f'negamax_ttm({u.id}, alpha={alpha0:2}, beta={beta:2}, depth={depth}, T={T0}) = {value:2} ({flag})')
    return value


def collect_nodes(u: Node) -> List[Node]:
    """
    Collect all unique nodes in the tree using depth-first traversal.

    Args:
        u: The root node of the game tree

    Returns:
        List[Node]: A list of all unique nodes in the tree
    """
    result = [u]
    for v in u.children:
        result.extend(collect_nodes(v))
    return list(set(result))


# --- helper: parse plain graphviz output into positions ---
def _parse_graphviz_plain_positions(plain_text: str) -> Dict[str, Tuple[float, float]]:
    """
    Parse the `plain` output of Graphviz (dot -Tplain) and return node positions.
    Returns a dict mapping node name -> (x, y) (floats).
    Coordinates are normalized so center is at (0,0) to produce nicer TikZ placement.
    """
    positions: Dict[str, Tuple[float, float]] = {}
    minx = miny = float('inf')
    maxx = maxy = float('-inf')

    for line in plain_text.splitlines():
        parts = line.split()
        if not parts:
            continue
        if parts[0] == 'node':
            # plain format: node <name> <x> <y> <width> <height> <label>
            name = parts[1]
            x = float(parts[2])
            y = float(parts[3])
            positions[name] = (x, y)
            if x < minx: minx = x
            if x > maxx: maxx = x
            if y < miny: miny = y
            if y > maxy: maxy = y

    # If no nodes found, return empty
    if not positions:
        return positions

    # Normalize: translate center to (0,0) for nicer TikZ coordinates.
    cx = (minx + maxx) / 2.0
    cy = (miny + maxy) / 2.0

    normalized = {}
    for name, (x, y) in positions.items():
        normalized[name] = (x - cx, y - cy)

    return normalized


def draw_tree_graphviz(u: Node, filename: str, visited=None, special=None, with_labels=False, return_positions: bool = False) -> Dict[str, Tuple[float, float]] or None:
    """
    Render the tree with Graphviz (PDF) and optionally return a dict of node positions
    computed by Graphviz (using the 'plain' output).
    If return_positions is True the function returns a dict mapping node-id -> (x, y).
    """
    V = collect_nodes(u)
    visited = [v.id for v in V] if visited is None else list(set(visited))
    special = special if special else []

    dot = graphviz.Digraph()
    dot.attr('graph', rankdir='TD')
    dot.attr('node', fontsize='12')

    # Create nodes
    for node in V:
        label = f'{node.id}={node.eval}' if with_labels else f'{node.eval}'
        attributes = {
            'label': label,
            'style': 'filled',
            'fillcolor': 'gray80' if node.color == Color.Black else 'white'
        }

        if node.id in special:
            attributes.update({
                'peripheries': '2',  # double border
            })
        elif node.id not in visited:
            attributes.update({
                'style': 'dotted,filled',  # Dotted outline
                'fontcolor': 'gray60'  # Muted label
            })
        dot.node(str(node.id), **attributes)

    # Draw nodes and edges
    for node in V:
        label = f'{node.id}={node.eval}' if with_labels else f'{node.eval}'
        attributes = {
            'label': label,
            'style': 'filled',
            'fillcolor': 'gray80' if node.color == Color.Black else 'white',
            'fontcolor': 'black'  # Always draw labels in black
        }

        if node.id in special:
            attributes.update({
                'peripheries': '2',  # double border
            })
        elif node.id not in visited:
            attributes.update({
                'style': 'dotted,filled',  # dotted outline
                # Do not override fontcolor here
            })

        dot.node(str(node.id), **attributes)

        # Draw edges
        for child in node.children:
            edge_style = 'dashed' if child.id not in visited else 'solid'
            dot.edge(str(node.id), str(child.id), style=edge_style)

    # Render PDF (as before)
    dot.render(filename, format='pdf', cleanup=True)

    if return_positions:
        # Ask graphviz for plain layout to parse computed coordinates.
        # Use the `pipe` interface with format='plain'
        plain_bytes = dot.pipe(format='plain')
        plain = plain_bytes.decode('utf-8')
        positions = _parse_graphviz_plain_positions(plain)
        return positions

    return None


# --- modified draw_tree_tikz: accept positions from graphviz ---
def draw_tree_tikz(u: Node, filename: str, visited=None, with_labels=False, positions: Dict[str, Tuple[float, float]] = None) -> None:
    """
    Generate a TikZ picture for a game tree.
    If `positions` is provided (a dict mapping node-id -> (x,y)), use those coordinates.
    Otherwise fall back to the previous rough depth/sibling layout.
    visited: nodes that have been visited (others are dashed)
    with_labels: if True, display node IDs top-left in math font
    """
    V = collect_nodes(u)
    visited = [v.id for v in V] if visited is None else list(set(visited))

    # If no positions supplied, compute rough positions as before
    if positions is None:
        # First pass to get all nodes and their depths
        nodes_by_depth = {}

        def get_depths(node, depth=0):
            nodes_by_depth.setdefault(depth, []).append(node)
            for child in node.children:
                get_depths(child, depth + 1)

        get_depths(u)

        # Assign positions level by level to avoid conflicts
        positions = {}
        max_depth = max(nodes_by_depth.keys()) if nodes_by_depth else 0

        for depth in sorted(nodes_by_depth.keys()):
            nodes_at_depth = nodes_by_depth[depth]
            spacing = 2.0
            total_width = (len(nodes_at_depth) - 1) * spacing
            start_x = -total_width / 2

            for i, node in enumerate(nodes_at_depth):
                x = start_x + i * spacing
                positions[node.id] = (x, -depth * 2)
    else:
        # positions provided by Graphviz: ensure all nodes are present
        # If a node is missing, fall back to (0,0) for that node (shouldn't normally happen)
        for node in V:
            if str(node.id) not in positions and node.id not in positions:
                positions[str(node.id)] = (0.0, 0.0)

    tikz_lines = []
    tikz_lines.append(r"\begin{tikzpicture}[>=stealth]")

    # Node definitions
    for node in V:
        # look up by string name; graphviz and our code use string ids
        key = str(node.id)
        x, y = positions.get(key, positions.get(node.id, (0.0, 0.0)))
        node_color = 'whiteplayer' if node.color == Color.White else 'blackplayer'
        node_style = f"{node_color}"
        if node.id not in visited:
            node_style += ",dashednode"
        # Main node with the numeric eval
        tikz_lines.append(f"\\node[gamenode,{node_style}] ({key}) at ({x:.2f},{y:.2f}) {{${node.eval}$}};")
        # Optional label node (unique name)
        if with_labels:
            tikz_lines.append(f"\\node[gamelabel] ({key}_label) at ({key}) {{${key}$}};")

    # Edges
    for node in V:
        for child in node.children:
            edge_style = "gamedashedge" if child.id not in visited else "gameedge"
            tikz_lines.append(f"\\draw[{edge_style}] ({node.id}) -- ({child.id});")

    tikz_lines.append(r"\end{tikzpicture}")

    # Write to file
    if not filename.endswith('.tikz'):
        filename += '.tikz'
    with open(filename, 'w') as f:
        f.write('\n'.join(tikz_lines))


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
    node_map = {x.id:x for x in collect_nodes(u)}
    return u, node_map


def run_negamax_ttm():
    u, node_map = make_tree()
    v = node_map['v']

    print('--- negamax_ttm_a ---')
    T = TranspositionTable()
    Settings.visited = []
    negamax_ttm(u, alpha=0, beta=5, depth=6, T=T)

    # Render graphviz and also get computed positions
    gv_positions = draw_tree_graphviz(u, 'negamax_ttm_a', visited=Settings.visited, special=['v'], return_positions=True)
    # Also produce with labels (but no need to re-get positions)
    draw_tree_graphviz(u, 'negamax_ttm_a_with_labels', visited=Settings.visited, special=['v'], with_labels=True)
    # Use graphviz positions when making the TikZ version
    draw_tree_tikz(u, 'negamax_ttm_a', visited=Settings.visited, with_labels=True, positions=gv_positions)
    print(f'T = {T}')

    print('--- negamax_ttm_b ---')
    T = TranspositionTable()
    Settings.visited = []
    negamax_ttm(v, alpha=0, beta=2, depth=4, T=T)
    gv_positions_b = draw_tree_graphviz(v, 'negamax_ttm_b', visited=Settings.visited, special=['v'], return_positions=True)
    draw_tree_graphviz(v, 'negamax_ttm_b', visited=Settings.visited)
    # If you want tikz here too, call:
    # draw_tree_tikz(v, 'negamax_ttm_b', visited=Settings.visited, positions=gv_positions_b)
    print(f'T = {T}')

    print('--- negamax_ttm_c ---')
    Settings.visited = []
    negamax_ttm(v, alpha=0, beta=5, depth=2, T=T)
    draw_tree_graphviz(v, 'negamax_ttm_c', visited=Settings.visited, special=['v'])
    # use Graphviz positions if you want a TikZ of this also:
    gv_positions_c = draw_tree_graphviz(v, 'negamax_ttm_c', visited=Settings.visited, return_positions=True)
    draw_tree_tikz(v, 'negamax_ttm_c', visited=Settings.visited, positions=gv_positions_c)
    print(f'T = {T}')


def run_negamax_ttw():
    u, node_map = make_tree()
    print('--- negamax_ttw ---')
    T = TranspositionTable()
    Settings.visited = []
    negamax_ttw(u, alpha=0, beta=5, depth=6, T=T)
    print(f'T = {T}')


if __name__ == '__main__':
    run_negamax_ttm()
    run_negamax_ttw()
