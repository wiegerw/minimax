// Copyright: Wieger Wesselink 2023
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)

include "definitions.dfy"

abstract module Lemmas
{
  import opened Definitions

  // Proves that slicing children up to i+1 equals slice up to i plus the i-th child
  lemma ChildrenAppendLemma(u: Node, i: nat)
    requires 0 <= i < |u.children|
    ensures u.children[..i+1] == u.children[..i] + [u.children[i]]
  {
  }

  // Proves that slicing all children equals the original children sequence
  lemma ChildrenFinalLemma(u: Node)
    ensures u.children[..|u.children|] == u.children
  {
  }

  // Proves that partial minimax result over all children equals full minimax result
  lemma PartialMinimaxABLemma(value: bounded_int, u: Node, i: nat, alpha: bounded_int, beta: bounded_int)
    requires i == |u.children| > 0
    requires is_partial_minimax_ab_result(value, u, i, alpha, beta)
    ensures is_minimax_ab_result(value, u, alpha, beta)
  {
  }

  // Proves that partial minimax over all children equals full minimax
  lemma PartialMinimaxLemma(u: Node)
    requires |u.children| > 0
    ensures partial_minimax(u, |u.children|) == minimax(u)
  {
    assert u.children[..|u.children|] == u.children;
  }

  // Proves that partial negamax over all children equals full negamax
  lemma PartialNegamaxLemma(u: Node)
    requires turn_based()
    requires |u.children| > 0
    ensures partial_negamax(u, |u.children|) == negamax(u)
  {
    reveal partial_negamax();
    assert u.children[..|u.children|] == u.children;
    NegamaxChildrenLemma(u);
    assert negamax(u) == -minimum(apply_negamax(u.children));
  }

  // Proves equivalence between minimax and negated negamax for Black nodes
  lemma MinimaxNegamaxLemma(v: seq<Node>)
      requires forall i | 0 <= i < |v| :: color(v[i]) == -1
      ensures apply_minimax(v) == negated(apply_negamax(v))
  {
    forall i | 0 <= i < |v| ensures apply_minimax(v)[i] == negated(apply_negamax(v))[i]
    {
      calc
      {
        negated(apply_negamax(v))[i];
        ==
        -apply_negamax(v)[i];
        ==
        -negamax(v[i]);
        ==
        minimax(v[i]);
        ==
        apply_minimax(v)[i];
      }
    }
  }

  // Proves equivalence between two alpha-beta result definitions
  lemma IsABResultLemma(value: bounded_int, x: bounded_int, alpha: bounded_int, beta: bounded_int)
    requires alpha < beta
    ensures is_ab_result(value, x, alpha, beta) <==> is_ab_result'(value, x, alpha, beta)
  {
  }  

  // Proves equivalence between two negamax definitions in turn-based games
  lemma NegamaxDefinitionsLemma(u: Node)
    requires turn_based()
    ensures negamax(u) == negamax'(u)
  {
  }

  // Proves negamax equals negative minimum of children's negamax values
  lemma NegamaxChildrenLemma(u: Node)
    requires turn_based()
    requires |u.children| > 0
    ensures negamax(u) == -minimum(apply_negamax(u.children))
  {
    if u.color == Black
    {
      assert apply_minimax(u.children) == apply_negamax(u.children);
    }  
    else
    {
      MinimaxNegamaxLemma(u.children);
      assert apply_minimax(u.children) == negated(apply_negamax(u.children));
    }
  }

  // Proves properties of depth truncation: preserves child count and recursive structure
  lemma TruncateLemma(u: Node, i: nat, depth: nat)
    requires 0 <= i < |u.children|
    requires depth > 0
    ensures |truncate_at_depth(u, depth).children| == |u.children|
    ensures truncate_at_depth(u, depth).children[i] == truncate_at_depth(u.children[i], depth - 1)
  { 
  }

  // Proves that partial negamax alpha-beta result over all children equals full result
  lemma PartialNegamaxAlphaBetaLemma(value: bounded_int, u: Node, i: nat, alpha: bounded_int, beta: bounded_int)
    requires turn_based()
    requires i == |u.children| > 0
    requires is_partial_negamax_ab_result(value, u, i, alpha, beta)
    ensures is_negamax_ab_result(value, u, alpha, beta)
  {
    reveal is_negamax_ab_result();
    PartialNegamaxLemma(u);
  }

  // Proves that every node is a subtree of itself (reflexivity)
  lemma SubtreeReflexivityLemma(u: Node)
    ensures is_partial_subtree(u, u)
  {
    var u_ := u.children;
    var index := iota(|u_|);
    assert is_subtree_index(index, u, u);
  }  

  // Helper lemma for subtree transitivity: proves index composition preserves subtree mapping
  // This lemma makes the proof much faster
  lemma SubtreeTransitivityHelperLemma(index1: seq<nat>, index2: seq<nat>, u: Node, v: Node, w: Node)
    requires is_subtree_index(index1, u, v)
    requires is_subtree_index(index2, v, w)
    ensures forall i | 0 <= i < |index1| :: 0 <= index1[i] < |index2|
    ensures is_subtree_index(compose_indices(index1, index2), u, w)
  {   
  }

  // Proves transitivity of subtree relation: if u is subtree of v and v is subtree of w, then u is subtree of w
  lemma SubtreeTransitivityLemma(u: Node, v: Node, w: Node)
    requires is_partial_subtree(u, v)
    requires is_partial_subtree(v, w)
    ensures is_partial_subtree(u, w)
  {
    var u_ := u.children;
    var v_ := v.children;
    var w_ := w.children;

    var index1: seq<nat> :|
      is_subtree_index(index1, u, v) && forall i | 0 <= i < |u_| :: && is_partial_subtree(u_[i], v_[index1[i]]);

    var index2: seq<nat> :|
      is_subtree_index(index2, v, w) && forall i | 0 <= i < |v_| :: && is_partial_subtree(v_[i], w_[index2[i]]);

    SubtreeTransitivityHelperLemma(index1, index2, u, v, w);
    var index3: seq<nat> := compose_indices(index1, index2);

    assert is_subtree_index(index3, u, w);
    assert forall i | 0 <= i < |u_| :: is_partial_subtree(u_[i], w_[index3[i]]);
  }

} // Lemmas
