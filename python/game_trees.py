# Copyright 2025 Wieger Wesselink.
# Distributed under the Boost Software License, Version 1.0.
# (See accompanying file LICENSE or http://www.boost.org/LICENSE_1_0.txt)

"""
This module provides data structures and utilities for working with game trees.

Game trees are used to represent the possible states and moves in a two-player
zero-sum game. This module includes functionality for creating, manipulating,
visualizing, and analyzing game trees for use with minimax algorithms.
"""

import copy
import itertools
import pathlib
import random
from enum import Enum
from pathlib import Path
from typing import Optional, List, Set, Dict, Tuple, FrozenSet, Generator, Any

import graphviz


Node = Any
Edge = Tuple[Node, Node]


class DirectedGraph:
    def nodes(self) -> Generator[Node, None, None]:
        raise NotImplementedError

    def edges(self) -> Generator[Edge, None, None]:
        raise NotImplementedError

    def add_node(self, u: Node) -> None:
        raise NotImplementedError

    def add_edge(self, e: Edge) -> None:
        raise NotImplementedError

    def remove_edge(self, e: Edge) -> None:
        raise NotImplementedError

    def __eq__(self, other: 'DirectedGraph') -> bool:
        V1 = set(self.nodes())
        E1 = set(self.edges())
        V2 = set(other.nodes())
        E2 = set(other.edges())
        return V1 == V2 and E1 == E2

    def __str__(self) -> str:
        nodes = ' '.join(str(u) for u in self.nodes())
        edges = ' '.join(f'({u},{v})' for (u, v) in self.edges())
        return f'nodes = {nodes}\nedges = {edges}'

    def pred(self, u: Node) -> Generator[Node, None, None]:
        raise NotImplementedError

    def succ(self, u: Node) -> Generator[Node, None, None]:
        raise NotImplementedError


def simple_topological_sort(G: DirectedGraph) -> List[Node]:
    order = []
    W = set(G.nodes())
    while len(W) > 0:
        for u in W:
            if set(G.pred(u)) <= set(order):
                break
        else:
            raise ValueError("Graph has at least one cycle or unresolved dependency")
        W.remove(u)
        order.append(u)
    return order


class Color(Enum):
    """
    Represents the player's color in a two-player game.
    
    In the context of minimax algorithms, White is the maximizing player (value 1),
    and Black is the minimizing player (value -1).
    
    Attributes:
        White: The maximizing player (value 1)
        Black: The minimizing player (value -1)
    """
    White = 1
    Black = -1


class Node(object):
    """
    Represents a node in a game tree.
    
    A node contains an evaluation value, a color indicating which player's turn it is,
    a list of child nodes representing possible moves, and an optional identifier.
    
    Attributes:
        color: The player whose turn it is at this node
        eval: The evaluation value of this position (higher is better for White)
        children: List of child nodes representing possible moves
        id: Optional identifier for the node
    """
    def __init__(self, color: Color, eval: int, children=None, id=None):
        """
        Initialize a game tree node.
        
        Args:
            color: The player whose turn it is at this node
            eval: The evaluation value of this position
            children: List of child nodes (default empty list)
            id: Optional identifier for the node
        """
        if children is None:
            children = []
        self.color = color
        self.eval = eval
        self.children = children
        self.id = id

    def __repr__(self):
        """
        Returns a string representation of the node.

        Returns:
            str: A string representation showing the node's id, color, evaluation, and children
        """
        child_ids = [repr(child.id) for child in self.children]
        return (f"Node(id={self.id!r}, color={self.color!r}, eval={self.eval}, "
                f"children=[{', '.join(child_ids)}])")


def truncate_at_depth(u: Node, depth: int) -> Node:
    """
    Creates a copy of the game tree truncated to a specified depth.
    
    Args:
        u: The root node of the game tree
        depth: The maximum depth to include
        
    Returns:
        Node: A new game tree with the same structure up to the specified depth
    """
    if depth == 0 or len(u.children) == 0:
        return Node(color=u.color, eval=u.eval, children=[], id=u.id)
    else:
        return Node(color=u.color, eval=u.eval, children=[truncate_at_depth(v, depth - 1) for v in u.children], id=u.id)


def tree_depth(u: Node) -> int:
    # Determine the maximum depth of the tree
    max_depth = 0
    nodes_at_depth = [u]
    while nodes_at_depth:
        max_depth += 1
        next_level = []
        for node in nodes_at_depth:
            next_level.extend(node.children)
        nodes_at_depth = next_level
    return max_depth


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


def find_nodes_at_depth(u: Node, depth: int) -> List[Node]:
    """
    Returns a list of all nodes at a given depth from the root node u.

    Args:
        u: The root node.
        depth: The distance from the root.

    Returns:
        A list of nodes at the given depth.
    """
    if depth == 0:
        return [u]
    result = []
    for v in u.children:
        result.extend(find_nodes_at_depth(v, depth - 1))
    return result


def replace_nodes(u: Node, sigma: Dict[Node, Node]) -> Node:
    """
    Create a new tree by replacing nodes according to substitution sigma.
    Nodes not in sigma are copied as-is with their children.
    """
    # If this node is in the substitution, use the replacement
    if u in sigma:
        return copy.deepcopy(sigma[u])

    # Otherwise, copy this node and recursively replace children
    new_children = [replace_nodes(child, sigma) for child in u.children]
    return Node(u.color, u.eval, new_children, u.id)


def generate_node_extensions(leaf: Node) -> List[Node]:
    """Generate all all-or-none extensions starting at a leaf node"""
    if not leaf.children:
        return [Node(leaf.color, leaf.eval, [], leaf.id)]

    # Option 1: Don't include any children
    extensions = [Node(leaf.color, leaf.eval, [], leaf.id)]

    # Option 2: Include all children (with their extensions)
    child_extension_products = []
    for child in leaf.children:
        child_extension_products.append(generate_node_extensions(child))

    for combination in itertools.product(*child_extension_products):
        extensions.append(Node(leaf.color, leaf.eval, list(combination), leaf.id))

    return extensions


def all_or_none_extensions(u: Node, d: int) -> List[Node]:
    """
    Generate all all-or-none extensions of node u up to depth d.
    - All nodes at depth <= d are preserved exactly
    - For nodes beyond depth d: either include all children or none
    - Returns complete trees with original structure up to depth d
    """
    # 1. Find all nodes at depth d (where extensions will start)
    extension_points = find_nodes_at_depth(u, d)

    # 2. Generate all possible extensions for each extension point
    extension_options = []
    for node in extension_points:
        options = generate_node_extensions(node)
        extension_options.append(options)

    # 3. Generate all possible substitution combinations
    extensions = []
    for combo in itertools.product(*extension_options):
        # Create substitution dictionary
        sigma = {}
        for original_node, extended_node in zip(extension_points, combo):
            sigma[original_node] = extended_node

        # Apply substitution to the original tree
        extended_tree = replace_nodes(u, sigma)
        extensions.append(extended_tree)

    return extensions


def make_random_game_tree(n: int, bound: int = 3) -> Node:
    """
    Generates a random game tree with n nodes.
    
    The tree is constructed by randomly selecting existing nodes as parents
    for new nodes, alternating colors between levels.
    
    Args:
        n: The number of nodes in the tree
        bound: Evaluations are in the interval [-bound, bound]
        
    Returns:
        Node: The root of a randomly generated game tree
        
    Raises:
        ValueError: If n is less than 1
    """
    if n == 0:
        raise ValueError("n must be greater than 0.")

    index = 0

    def make_node(color: Color) -> Node:
        nonlocal index
        node = Node(color=color, eval=random.randint(-bound, bound), children=None, id=index)
        index = index + 1
        return node

    root = make_node(Color.White)
    nodes_in_tree = [root]

    for _ in range(n - 1):
        parent = random.choice(nodes_in_tree)
        color = Color.White if parent.color == Color.Black else Color.Black
        node = make_node(color)
        parent.children.append(node)
        nodes_in_tree.append(node)

    return root


def find_nodes_ids(u: Node, depth: int) -> list[int]:
    """
    Collects the IDs of all nodes in the tree up to a specified depth.
    
    Args:
        u: The root node of the game tree
        depth: The maximum depth to search
        
    Returns:
        list[int]: A list of node IDs found within the specified depth
    """
    result = [u.id]
    if depth > 0:
        for v in u.children:
            result.extend(find_nodes_ids(v, depth - 1))
    return result


def all_subsets(W):
    """
    Generates all possible subsets of a collection.
    
    Args:
        W: The collection to generate subsets from
        
    Returns:
        list: A list of all possible subsets of W
    """
    subsets = []
    for r in range(len(W) + 1):
        subsets.extend(itertools.combinations(W, r))
    return subsets


def restrict(u: Node, ids: set[int]) -> Node:
    """
    Creates a copy of the game tree with only the nodes whose IDs are in the given set.
    
    Args:
        u: The root node of the game tree
        ids: A set of node IDs to keep
        
    Returns:
        Node: A new game tree containing only nodes with IDs in the given set
    """
    u1 = copy.deepcopy(u)
    for v in collect_nodes(u1):
        v.children = [w for w in v.children if w.id in ids]
    return u1


def all_extensions(u: Node, min_depth: int) -> list[Node]:
    """
    Generates all possible extensions of a game tree beyond a minimum depth.
    
    This function creates variations of the tree by including different
    combinations of nodes beyond the minimum depth.
    
    Args:
        u: The root node of the game tree
        min_depth: The minimum depth that must be included in all extensions
        
    Returns:
        list[Node]: A list of game trees representing all possible extensions
    """
    result = []
    U = set(find_nodes_ids(u, min_depth))
    V = set(find_nodes_ids(u, 100000))
    for X in all_subsets(V - U):
        Y = U | set(X)
        result.append(restrict(u, Y))
    return result


def draw_tree(u: Node, filename: str, visited=None, special=None) -> None:
    def collect_nodes(u: Node) -> List[Node]:
        result = [u]
        for v in u.children:
            result.extend(collect_nodes(v))
        return list(dict.fromkeys(result))  # preserve order, remove duplicates

    V = collect_nodes(u)
    visited = [v.id for v in V] if visited is None else list(set(visited))
    special = special if special else []

    dot = graphviz.Digraph()
    dot.attr('graph', rankdir='TD')
    dot.attr('node', fontsize='12')

    # Create nodes
    for node in V:
        # label = f'id={node.id}\neval={node.eval}'
        label = f'{node.eval}'
        attributes = {'label': label}
        if node.id in special:
            attributes['style'] = 'filled'
            attributes['fillcolor'] = 'orangered'
        elif node.id not in visited:
            attributes['style'] = 'filled'
            attributes['fillcolor'] = 'yellow'
        elif node.color == Color.Black:
            attributes['style'] = 'filled'
            attributes['fillcolor'] = 'lightgray'
        dot.node(str(node.id), **attributes)

    # Add edges with ordered subgraphs
    for node in V:
        if len(node.children) > 1:
            # Create a subgraph to preserve the order of children
            with dot.subgraph() as s:
                s.attr(rank='same')  # Place on the same rank (horizontal)
                for child in node.children:
                    s.node(str(child.id))
                for i in range(len(node.children) - 1):
                    # Add invisible edges to enforce order
                    s.edge(str(node.children[i].id), str(node.children[i + 1].id), style='invis')

        # Add visible edges from parent to children
        for child in node.children:
            dot.edge(str(node.id), str(child.id))

    dot.render(filename, format='pdf', cleanup=True)


def print_tree(root: Node) -> str:
    """
    Converts a game tree to a string in gtree format.
    
    The gtree format represents each node on a separate line with:
    - Node ID
    - Evaluation value
    - Color (W for White, B for Black)
    - List of child node IDs
    
    Args:
        root: The root node of the game tree
        
    Returns:
        str: A string representation of the tree in gtree format
    """
    nodes = collect_nodes(root)
    lines = []

    for node in nodes:
        line_parts = [str(node.id), str(node.eval)]

        if node.color is not None:
            line_parts.append('W' if node.color == Color.White else 'B')

        if node.children:
            line_parts.extend(str(child.id) for child in node.children)

        lines.append(' '.join(line_parts))

    return '\n'.join(lines)


def write_tree(root: Node, filename: Path) -> None:
    """
    Writes a game tree to a file in gtree format.
    
    Args:
        root: The root node of the game tree
        filename: The path to the output file
    """
    text = print_tree(root)
    filename.write_text(text)


def print_nodes(msg: str, nodes: List[Node]) -> None:
    """
    Prints a message followed by a list of nodes.
    
    Args:
        msg: The message to print
        nodes: The list of nodes to print
    """
    print(msg)
    for node in nodes:
        print(node)


def parse_tree(text: str) -> Node:
    """
    Parses a string in gtree format into a game tree.
    
    Args:
        text: The string in gtree format
        
    Returns:
        Node: The root node of the parsed game tree
        
    Raises:
        ValueError: If the input text is empty
    """
    def fill_missing_colors(node: Node, parent_color: Optional[Color] = None) -> None:
        """
        Fill in missing colors based on parent (root defaults to White).
        
        Args:
            node: The node to fill color for
            parent_color: The color of the parent node
        """
        if node.color is None:
            node.color = (
                Color.White
                if parent_color is None or parent_color == Color.Black
                else Color.Black
            )

        for child in node.children:
            fill_missing_colors(child, node.color)

    def split_text(text: str) -> List[str]:
        """
        Split text and return non-empty, stripped lines.
        
        Args:
            text: The input text
            
        Returns:
            List[str]: A list of non-empty, stripped lines
        """
        lines = text.splitlines()
        return [line.strip() for line in lines if line.strip()]

    def create_nodes_from_lines(lines: list[str]) -> Dict[str, Node]:
        """
        Create nodes from lines of text.
        
        Args:
            lines: Lines of text in gtree format
            
        Returns:
            Dict[str, Node]: A dictionary mapping node IDs to nodes
        """
        nodes = {}
        for line in lines:
            line = line.strip()
            parts = line.split()
            id = parts[0]
            eval_ = int(parts[1])
            nodes[id] = Node(color=None, eval=eval_, id=id)
        return nodes

    def finish_nodes(lines: list[str], nodes: Dict[str, Node]):
        """
        Complete node initialization by setting colors and adding children.
        
        Args:
            lines: Lines of text in gtree format
            nodes: Dictionary mapping node IDs to nodes
        """
        for line in lines:
            line = line.strip()
            parts = line.split()
            u_id = parts[0]
            u = nodes[u_id]
            if len(parts) >= 3 and parts[2] in ('W', 'B'):
                u.color = Color.White if parts[2] == 'W' else Color.Black
                child_ids = parts[3:]
            else:
                child_ids = parts[2:]
            for id in child_ids:
                u.children.append(nodes[id])

    lines = split_text(text)
    if not lines:
        raise ValueError("Empty tree file")
    nodes = create_nodes_from_lines(lines)
    finish_nodes(lines, nodes)
    root_id = lines[0].split()[0]
    root = nodes[root_id]
    fill_missing_colors(root)
    return root


def read_tree(filename: Path) -> Node:
    """
    Reads a game tree from a file in gtree format.
    
    Args:
        filename: The path to the input file
        
    Returns:
        Node: The root node of the parsed game tree
    """
    text = pathlib.Path(filename).read_text()
    return parse_tree(text)


class GameTreeGraph(DirectedGraph):
    """
    A directed graph representation of a game tree.
    
    Attributes:
        _nodes: A list of all nodes in the game tree
    """
    def __init__(self, root: Node) -> None:
        """
        Initialize a graph from a game tree.
        
        Args:
            root: The root node of the game tree
        """
        self._nodes = collect_nodes(root)

    def pred(self, v: Node) -> Generator[Node, None, None]:
        """
        Get all predecessors (parents) of a node.
        
        Args:
            v: The node to find predecessors for
            
        Yields:
            Node: Each predecessor node
        """
        for u in self._nodes:
            if v in u.children:
                yield u

    def succ(self, u: Node) -> Generator[Node, None, None]:
        """
        Get all successors (children) of a node.
        
        Args:
            u: The node to find successors for
            
        Yields:
            Node: Each successor node
        """
        yield from u.children

    def nodes(self) -> Generator[Node, None, None]:
        """
        Get all nodes in the graph.
        
        Yields:
            Node: Each node in the graph
        """
        yield from self._nodes

    def edges(self) -> Generator[Edge, None, None]:
        """
        Get all edges in the graph.
        
        Yields:
            Edge: Each edge as a (source, target) tuple
        """
        for u in self._nodes:
            for v in u.children:
                yield (u, v)

    def assign_equivalence_ids(self) -> None:
        """
        Assigns new ids to the nodes. Nodes in the same equivalence
        class get the same id.
        
        This is useful for identifying structurally equivalent subtrees.
        """
        classes = equivalence_classes(self)
        for i, eq_class in enumerate(classes):
            for node in eq_class:
                node.id = i

    def assign_unique_ids(self) -> None:
        """
        Assigns new, unique ids to the nodes.
        
        This ensures that each node has a unique identifier.
        """
        for i, node in enumerate(self._nodes):
            node.id = i


def equivalence_classes(G: GameTreeGraph) -> Set[FrozenSet[Node]]:
    """
    Groups nodes into equivalence classes based on their structure.
    
    Two nodes are considered equivalent if they have the same color, evaluation,
    and their children are equivalent (recursively). This function uses a
    bottom-up approach, starting from the leaves and working up to the root.
    
    Args:
        G: The game tree graph
        
    Returns:
        Set[FrozenSet[Node]]: A set of equivalence classes, where each class
                             is a frozenset of equivalent nodes
    """
    signature_to_class: Dict[Tuple, Set[Node]] = {}
    node_to_signature: Dict[Node, Tuple] = {}

    order = simple_topological_sort(G)
    order = list(reversed(order))  # We need to start at the leaves

    for node in order:
        # Create a tuple of the equivalence class identifiers of the children
        child_sigs = tuple(sorted(node_to_signature[child] for child in node.children))
        signature = (node.color, node.eval, child_sigs)

        # Find or create the equivalence class for this signature
        if signature not in signature_to_class:
            signature_to_class[signature] = set()
        signature_to_class[signature].add(node)

        # Store the signature for this node
        node_to_signature[node] = signature

    return set(frozenset(eq_class) for eq_class in signature_to_class.values())
