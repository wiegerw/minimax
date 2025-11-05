// Copyright: Wieger Wesselink 2023
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)

// Core definitions for minimax and negamax game tree algorithms
// Defines game tree nodes, evaluation functions, and alpha-beta pruning predicates
abstract module Definitions
{
  type pos = n: int | n > 0 witness 1
  const UNSPECIFIED_POSITIVE_NUMBER: pos
  const INFINITY: int := UNSPECIFIED_POSITIVE_NUMBER
  type bounded_int = x: int | -INFINITY <= x <= INFINITY

  datatype Color = White | Black  // Player colors in turn-based games
  datatype Node = Node_(eval: bounded_int, color: Color, children: seq<Node>)  // Game tree node

  // Transposition table entries for memoization
  datatype Flag = Lowerbound | Upperbound | Exact
  datatype TableEntry = TableEntry_(depth: nat, value: bounded_int, flag: Flag)
  type TranspositionTable = map<Node, TableEntry>

  // Replaces the i-th child with v
  function replace_child(u: Node, i: nat, v: Node): Node
    requires 0 <= i < |u.children|
  {
    Node_(u.eval, u.color, u.children[i := v])
  }  

  // Truncates game tree at specified depth, removing all nodes beyond that depth
  function truncate_at_depth(u: Node, depth: nat): Node
    ensures depth > 0 ==> |u.children| == |truncate_at_depth(u, depth).children|
  {
    var children := if depth == 0 then [] else truncate_at_depth_list(u.children, depth - 1);
    Node_(u.eval, u.color, children)
  }

  // Applies depth truncation to a sequence of nodes
  function truncate_at_depth_list(v: seq<Node>, depth: nat): seq<Node>
    ensures |truncate_at_depth_list(v, depth)| == |v|
    ensures forall i | 0 <= i < |v| :: truncate_at_depth_list(v, depth)[i] == truncate_at_depth(v[i], depth)
  {
    if |v| == 0 then []
    else truncate_at_depth_list(v[..|v|-1], depth) + [truncate_at_depth(v[|v|-1], depth)]
  }

  // Predicate ensuring alternating player colors in game tree (turn-based games)
  ghost predicate turn_based()
  {
    forall u: Node, v: Node | v in u.children :: color(v) == -color(u)
  }

  // Converts node color to numeric representation: White=1, Black=-1
  function color(u: Node): int
  {
    if u.color == Color.White then 1 else -1
  }

  // Returns the minimum of two integers
  function min(x: int, y: int): int
  {
    if x < y then x else y
  }

  // Returns the maximum of two integers
  function max(x: int, y: int): int
  {
    if x > y then x else y
  }

  // Returns the minimum value in a non-empty sequence
  function minimum(a: seq<int>): int
    requires |a| > 0
    ensures forall i | 0 <= i < |a| :: a[i] >= minimum(a)
    ensures exists i | 0 <= i < |a| :: a[i] == minimum(a)
  {
    if |a| == 1
    then a[0]
    else
      var m := minimum(a[..|a|-1]);
      if a[|a|-1] > m then m else a[|a|-1]
  }

  // Returns the maximum value in a non-empty sequence
  function maximum(a: seq<int>): int
    requires |a| > 0
    ensures forall i | 0 <= i < |a| :: a[i] <= maximum(a)
    ensures exists i | 0 <= i < |a| :: a[i] == maximum(a)
  {
    if |a| == 1
    then a[0]
    else
      var m := maximum(a[..|a|-1]);
      if a[|a|-1] < m then m else a[|a|-1]
  }

  // Returns minimum of bounded sequence, or INFINITY if empty
  ghost function minimum'(a: seq<bounded_int>): bounded_int
    ensures forall i | 0 <= i < |a| :: a[i] >= minimum'(a)
    ensures |a| > 0 ==> exists i | 0 <= i < |a| :: a[i] == minimum'(a)
    ensures |a| == 0 ==> INFINITY == minimum'(a)
  {
    if |a| == 0
    then INFINITY
    else minimum(a)
  }

  // Returns maximum of bounded sequence, or -INFINITY if empty
  ghost function maximum'(a: seq<bounded_int>): bounded_int
    ensures forall i | 0 <= i < |a| :: a[i] <= maximum'(a)
    ensures |a| > 0 ==> exists i | 0 <= i < |a| :: a[i] == maximum'(a)
    ensures |a| == 0 ==> -INFINITY == maximum'(a)
  {
    if |a| == 0
    then -INFINITY
    else maximum(a)
  }

  // Classic minimax evaluation: minimizing for Black, maximizing for White
  function minimax(u: Node): bounded_int
  {
    if |u.children| == 0
    then u.eval
    else
      if u.color == Black then
        minimum(apply_minimax(u.children))
      else      
        maximum(apply_minimax(u.children))
  }

  // Alternative negamax definition using color multiplication
  function negamax'(u: Node): bounded_int
  {
    if |u.children| == 0
    then color(u) * u.eval
    else
      -minimum(apply_negamax(u.children))
  }

  // Negamax evaluation: simplified minimax using color sign flipping
  // We use this alternative definition of negamax, since it makes the
  // proofs easier
  function negamax(u: Node): bounded_int
  {
    color(u) * minimax(u)
  }

  // Applies minimax evaluation to each node in a sequence
  function apply_minimax(v: seq<Node>): seq<bounded_int>
    ensures |apply_minimax(v)| == |v|
    ensures forall i | 0 <= i < |v| :: apply_minimax(v)[i] == minimax(v[i])
  {
    if |v| == 0 then []
    else apply_minimax(v[..|v|-1]) + [minimax(v[|v|-1])]
  }

  // Applies negamax evaluation to each node in a sequence
  function apply_negamax(v: seq<Node>): seq<bounded_int>
    ensures |apply_negamax(v)| == |v|
    ensures forall i | 0 <= i < |v| :: apply_negamax(v)[i] == negamax(v[i])
  {
    if |v| == 0 then []
    else apply_negamax(v[..|v|-1]) + [negamax(v[|v|-1])]
  }

  // Returns sequence with all elements negated
  function negated(a: seq<int>): seq<int>
    ensures |negated(a)| == |a|
    ensures forall i | 0 <= i < |a| :: negated(a)[i] == -a[i]
  {
    if |a| == 0 then []
    else [-a[0]] + negated(a[1..])
  }

  // Predicate defining valid alpha-beta result: x approximates exact value e within bounds
  // `e` is an exact minimax or negamax value
  // `x` is an approximation
  ghost predicate is_ab_result(x: bounded_int, e: bounded_int, alpha: bounded_int, beta: bounded_int)
  {
    e <= x <= alpha || alpha < e == x < beta || beta <= x <= e
  }

  // Alternative formulation of alpha-beta result predicate used in literature
  ghost predicate is_ab_result'(x: bounded_int, e: bounded_int, alpha: bounded_int, beta: bounded_int)
  {
    (x <= alpha ==> e <= x) &&
    ((alpha < x < beta) ==> x == e) &&
    (x >= beta ==> e >= x)
  }

  // Predicate for valid minimax alpha-beta result
  ghost predicate is_minimax_ab_result(value: bounded_int, u: Node, alpha: bounded_int, beta: bounded_int)
  {
    is_ab_result(value, minimax(u), alpha, beta)
  }

  // Predicate for valid negamax alpha-beta result
  opaque ghost predicate is_negamax_ab_result(value: bounded_int, u: Node, alpha: bounded_int, beta: bounded_int)
  {
    is_ab_result(value, negamax(u), alpha, beta)
  }

  // Computes minimax value considering only first i children
  ghost function partial_minimax(u: Node, i: nat): bounded_int
    requires 0 <= i <= |u.children|
  {
    if u.color == Black then
      minimum'(apply_minimax(u.children[..i]))
    else
      maximum'(apply_minimax(u.children[..i]))
  }

  // Predicate for valid partial minimax alpha-beta result
  ghost predicate is_partial_minimax_ab_result(value: bounded_int, u: Node, i: nat, alpha: bounded_int, beta: bounded_int)
    requires 0 <= i <= |u.children|
  {
    is_ab_result(value, partial_minimax(u, i), alpha, beta)
  }

  // Computes negamax value considering only first i children
  opaque ghost function partial_negamax(u: Node, i: nat): bounded_int
    requires 0 <= i <= |u.children|
  {
    -minimum'(apply_negamax(u.children[..i]))
  }

  // Proves equivalence between partial negamax and maximum of negated values
  lemma PartialNegamaxEquivalenceLemma(u: Node, i: nat)
    requires 0 <= i <= |u.children|
    ensures partial_negamax(u, i) == maximum'(negated(apply_negamax(u.children[..i])))
  {
    reveal partial_negamax();
  }

  // Predicate for valid partial negamax alpha-beta result
  ghost predicate is_partial_negamax_ab_result(value: bounded_int, u: Node, i: nat, alpha: bounded_int, beta: bounded_int)
    requires 0 <= i <= |u.children|
  {
    is_ab_result(value, partial_negamax(u, i), alpha, beta)
  }

  // Composes two index sequences for subtree mapping transitivity
  ghost function compose_indices(index1: seq<nat>, index2: seq<nat>): seq<nat>
    requires forall i | 0 <= i < |index1| :: 0 <= index1[i] < |index2|
    ensures |compose_indices(index1, index2)| == |index1|
    ensures forall i | 0 <= i < |index1| :: compose_indices(index1, index2)[i] == index2[index1[i]]
  {
    if index1 == [] then []
    else [index2[index1[0]]] + compose_indices(index1[1..], index2)
  }

  // Returns sequence [0, 1, ..., n - 1] for identity index mapping
  ghost function iota(n: nat): seq<nat>
    ensures |iota(n)| == n
    ensures forall i | 0 <= i < |iota(n)| :: iota(n)[i] == i
  {
    if n == 0 then []
    else iota(n - 1) + [n - 1]
  }

  // Predicate defining valid index mapping for subtree relationships
  // Maps the children of u to the children of v. The mapping is
  // injective and order preserving.
  //
  // N.B. Moving this into a separate predicate is essential for the verification.
  ghost predicate is_subtree_index(index: seq<nat>, u: Node, v: Node)
  {
    (|index| == |u.children|) && 
    (forall i | 0 <= i < |index| :: 0 <= index[i] < |v.children|) &&
    (forall i, j | 0 <= i < j < |index| :: index[i] < index[j])
  }

  // Predicate defining when node u is a partial subtree of node v
  // u is a subtree of v
  ghost predicate is_partial_subtree(u: Node, v: Node)
    decreases u, v
  {
    u.eval == v.eval &&
    u.color == v.color &&

    // Map the children of u to the children of v
    exists index: seq<nat> ::
      is_subtree_index(index, u, v) &&
      forall i | 0 <= i < |u.children| :: is_partial_subtree(u.children[i], v.children[index[i]])
  }

} // module Definitions
