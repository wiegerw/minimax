// Copyright: Wieger Wesselink 2023
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)

include "definitions.dfy"
include "lemmas.dfy"

// Negamax with transposition table for memoization and enhanced pruning
// https://en.wikipedia.org/wiki/Negamax

abstract module NegamaxTTWModule refines NegamaxTTWCommonModule
{
  // The Wikipedia 2025 version of negamax with a transposition table
  class NegamaxTTW
  {
    var T: TranspositionTable  // Memoization table for previously computed positions

    // Negamax with transposition table: caches results to avoid recomputation
    method Negamax(u: Node, alpha0: bounded_int, beta0: bounded_int, depth:nat)
      returns (result: bounded_int)
      modifies this`T
      requires alpha0 < beta0
      requires turn_based()
      requires is_valid_table(T)
      ensures is_negamax_tt_result(result, u, alpha0, beta0, depth)
      ensures is_valid_table(T)
    {
      var alpha, beta := alpha0, beta0;
      if u in T.Keys
      {
        var t := T[u];
        if t.depth >= depth && ((t.flag == Lowerbound && t.value >= beta) ||
            (t.flag == Exact) || (t.flag == Upperbound && t.value <= alpha))
        {
          TableLookupReturnLemma(u, alpha, beta, depth, t, T);
          return t.value;
        }
      }
      if depth == 0 || |u.children| == 0
      {
        DepthZeroReturnLemma(u, depth, alpha0, beta0);
        return color(u) * u.eval;
      }
      var value: bounded_int := -INFINITY;
      for i := 0 to |u.children|
        invariant is_valid_table(T)
        invariant 0 <= i <= |u.children|
        invariant i == 0 ==> value == -INFINITY && alpha == alpha0
        invariant alpha0 <= alpha < beta0
        invariant value <= alpha0 ==> alpha == alpha0
        invariant alpha0 < value < beta0 ==> value == alpha
        invariant i > 0 ==> exists u': Node :: is_expansion(u', u, depth) && is_partial_negamax_ab_result(value, u', i, alpha0, beta0)
        invariant i == |u.children| ==> is_negamax_tt_result(value, u, alpha0, beta0, depth)
      {
        ghost var old_alpha := alpha;
        ghost var old_value := value;
        var v := u.children[i];
        var negamax_v := Negamax(v, -beta, -alpha, depth - 1);
        value := max(value, -negamax_v);
        alpha := max(alpha, value);
        if alpha >= beta
        {
          LoopBreakLemma(u, v, i, depth, alpha0, beta0, old_alpha, old_value, alpha, value, negamax_v);
          break;
        }
        LoopMaintenanceLemma(u, v, i, depth, alpha0, beta0, old_alpha, old_value, alpha, value, negamax_v);
      }
      TableUpdateLemma(value, u, alpha0, beta0, depth, T);
      if value <= alpha0      {T := T[u:=TableEntry_(depth,value,Upperbound)];}
      else if alpha0 < value < beta0 {T:=T[u:=TableEntry_(depth,value,Exact)];}
      else if value >= beta0  {T := T[u:=TableEntry_(depth,value,Lowerbound)];}
      return value;
    }
  }

  lemma LoopBreakLemma2(u: Node, u': Node, v: Node, v': Node, i: nat, depth: nat, alpha0: bounded_int, beta0: bounded_int, old_alpha: bounded_int, old_value: bounded_int, alpha: bounded_int, value: bounded_int, negamax_v: bounded_int)
    requires turn_based()
    requires 0 <= i < |u.children|
    requires |u.children| == |u'.children|
    requires u' == replace_child(u, i, v')
    requires alpha >= beta0
    requires alpha0 <= old_alpha < beta0
    requires value == max(old_value, -negamax_v)
    requires alpha == max(old_alpha, value)
    requires is_negamax_ab_result(negamax_v, v', -beta0, -old_alpha)
    requires is_partial_negamax_ab_result(old_value, u, i, alpha0, beta0)
    ensures is_negamax_ab_result(value, u', alpha0, beta0)
  {
    reveal is_negamax_ab_result();
    reveal partial_negamax();

    MinMaxLemma(u', i);
    assert partial_negamax(u', i + 1) == max(partial_negamax(u', i), -negamax(v'));
    assert partial_negamax(u', i + 1) >= beta0;
    assert value >= beta0;
    PartialNegamaxLemma(u');
  }

  lemma LoopBreakLemma(u: Node, v: Node, i: nat, depth: nat, alpha0: bounded_int, beta0: bounded_int, old_alpha: bounded_int, old_value: bounded_int, alpha: bounded_int, value: bounded_int, negamax_v: bounded_int)
    requires turn_based()
    requires 0 <= i < |u.children|
    requires depth > 0
    requires v == u.children[i]
    requires alpha >= beta0
    requires alpha0 <= old_alpha < beta0
    requires value == max(old_value, -negamax_v)
    requires alpha == max(old_alpha, value)
    requires is_negamax_tt_result(negamax_v, v, -beta0, -old_alpha, depth - 1)
    requires i == 0 ==> old_value == -INFINITY && old_alpha == alpha0
    requires i > 0 ==>
      exists u': Node :: 
        is_expansion(u', u, depth) &&
        is_partial_negamax_ab_result(old_value, u', i, alpha0, beta0)
    ensures is_negamax_tt_result(value, u, alpha0, beta0, depth)
  {
    var v': Node :|
      is_expansion(v', v, depth - 1) &&
      is_negamax_ab_result(negamax_v, v', -beta0, -old_alpha);

    if i > 0 
    {
      var u': Node :|
        is_expansion(u', u, depth) &&
        is_partial_negamax_ab_result(old_value, u', i, alpha0, beta0);
  
      var u'' := replace_child(u', i, v');
      assert is_expansion(u'', u, depth);

      LoopBreakLemma2(u', u'', v, v', i, depth, alpha0, beta0, old_alpha, old_value, alpha, value, negamax_v);
      assert is_negamax_ab_result(value, u'', alpha0, beta0);
    }
    else
    {
      reveal partial_negamax();
      var u' := replace_child(u, i, v');

      LoopBreakLemma2(u, u', v, v', i, depth, alpha0, beta0, old_alpha, old_value, alpha, value, negamax_v);
      assert is_negamax_ab_result(value, u', alpha0, beta0);

      ExpansionReplaceChildLemma(u, u', v, v', i, depth);
      assert is_expansion(u', u, depth);

      assert is_negamax_ab_result(value, u', alpha0, beta0);
    }
  }

  lemma LoopMaintenanceLemma2(u': Node, u'': Node, v: Node, v': Node, i: nat, depth: nat, alpha0: bounded_int, beta0: bounded_int, old_alpha: bounded_int, old_value: bounded_int, alpha: bounded_int, value: bounded_int, negamax_v: bounded_int)
    requires 0 <= i < |u'.children|
    requires |u'.children| == |u''.children|
    requires u'' == replace_child(u', i, v')
    requires alpha < beta0
    requires old_value <= alpha0 ==> old_alpha == alpha0
    requires alpha0 <= old_alpha < beta0
    requires alpha0 < old_value < beta0 ==> old_alpha == old_value
    requires value == max(old_value, -negamax_v)
    requires alpha == max(old_alpha, value)
    requires is_negamax_ab_result(negamax_v, v', -beta0, -old_alpha)
    requires is_partial_negamax_ab_result(old_value, u', i, alpha0, beta0)
    ensures is_partial_negamax_ab_result(value, u'', i + 1, alpha0, beta0)
  {
    reveal is_negamax_ab_result();
    reveal partial_negamax();
    
    assert negamax(v') <= -beta0 <==> negamax_v <= -beta0;
    assert -beta0 < negamax(v') < -old_alpha <==> -beta0 < negamax_v == negamax(v') < -old_alpha;
    assert negamax(v') >= -old_alpha <==> negamax_v >= -old_alpha;
    assert value == max(old_value, -negamax_v);
    assert alpha == max(old_alpha, value);
    MinMaxLemma(u'', i);
    assert partial_negamax(u'', i + 1) == max(partial_negamax(u'', i), -negamax(u''.children[i]));
    assert partial_negamax(u'', i + 1) == max(partial_negamax(u'', i), -negamax(v'));
    assert partial_negamax(u'', i + 1) < beta0;
    assert value < beta0;
  }

  lemma LoopMaintenanceLemma(u: Node, v: Node, i: nat, depth: nat, alpha0: bounded_int, beta0: bounded_int, old_alpha: bounded_int, old_value: bounded_int, alpha: bounded_int, value: bounded_int, negamax_v: bounded_int)
    requires turn_based()
    requires 0 <= i < |u.children|
    requires depth > 0
    requires v == u.children[i]
    requires alpha0 <= old_alpha < beta0
    requires old_value <= alpha0 ==> old_alpha == alpha0
    requires alpha < beta0
    requires alpha0 < old_value < beta0 ==> old_alpha == old_value
    requires value == max(old_value, -negamax_v)
    requires alpha == max(old_alpha, value)
    requires is_negamax_tt_result(negamax_v, v, -beta0, -old_alpha, depth - 1)
    requires i == 0 ==> old_value == -INFINITY && old_alpha == alpha0
    requires i > 0 ==>
      exists u': Node :: 
        is_expansion(u', u, depth) &&
        is_partial_negamax_ab_result(old_value, u', i, alpha0, beta0)

    ensures
      exists u': Node :: 
        is_expansion(u', u, depth) &&
        is_partial_negamax_ab_result(value, u', i + 1, alpha0, beta0)

    ensures i == |u.children| - 1 ==> is_negamax_tt_result(value, u, alpha0, beta0, depth)
  {
    reveal is_negamax_ab_result();

    var v': Node :|
      is_expansion(v', v, depth - 1) &&
      is_negamax_ab_result(negamax_v, v', -beta0, -old_alpha);

    if i > 0
    {
      var u': Node :|
        is_expansion(u', u, depth) &&
        is_partial_negamax_ab_result(old_value, u', i, alpha0, beta0);

      var u'' := replace_child(u', i, v');
      assert is_expansion(u'', u, depth);

      LoopMaintenanceLemma2(u', u'', v, v', i, depth, alpha0, beta0, old_alpha, old_value, alpha, value, negamax_v);

      if i == |u.children| - 1
      {
        assert is_partial_negamax_ab_result(value, u'', i + 1, alpha0, beta0);
        PartialNegamaxAlphaBetaLemma(value, u'', i + 1, alpha0, beta0);
        assert is_negamax_ab_result(value, u'', alpha0, beta0);
      }
    }
    else
    {
      reveal partial_negamax();
      var u' := replace_child(u, i, v');
      ExpansionReplaceChildLemma(u, u', v, v', i, depth);
      assert is_expansion(u', u, depth);

      LoopMaintenanceLemma2(u, u', v, v', i, depth, alpha0, beta0, old_alpha, old_value, alpha, value, negamax_v);
      if i == |u.children| - 1
      {
        assert is_partial_negamax_ab_result(value, u', i + 1, alpha0, beta0);
        PartialNegamaxAlphaBetaLemma(value, u', i + 1, alpha0, beta0);
        assert is_negamax_ab_result(value, u', alpha0, beta0);
      }
    }
  }

} // module NegamaxTTWModule

// This module contains common functionality for the NegamaxTTW variations
abstract module NegamaxTTWCommonModule
{
  import opened Definitions
  import opened Lemmas

  // This models an all or nothing expansion. We have that u' is an expansion of truncate_at_depth(u, depth),
  // such that nodes at distance greater than depth to the root u have either all children included or none.
  predicate is_expansion(u': Node, u: Node, depth: nat)
  {
    var v := u.children;
    var v' := u'.children;

    u.eval == u'.eval && 
    u.color == u'.color &&
    if depth > 0
    then
      |v| == |v'| && forall i | 0 <= i < |v| :: is_expansion(v'[i], v[i], depth - 1)
    else
      |v'| == 0 ||
      (
        |v| == |v'| && forall i | 0 <= i < |v| :: is_expansion(v'[i], v[i], 0)
      )
  }

  // An expansion must include the truncated tree
  lemma ExpansionInludesTruncatedTreeLemma(u': Node, u: Node, depth: nat)
    requires is_expansion(u', u, depth)
    ensures truncate_at_depth(u, depth) == truncate_at_depth(u', depth)
  {
  }

  // An expansion must be a subtree
  lemma ExpansionIsSubtreeLemma(u': Node, u: Node, depth: nat)
    requires is_expansion(u', u, depth)
    ensures is_partial_subtree(u', u)
  {
    var v := u.children;
    var v' := u'.children;

    assert u.eval == u'.eval;
    assert u.color == u'.color;

    if depth > 0
    {
      var index := iota(|v'|);
      assert is_subtree_index(index, u', u);
    }
    else
    {
      if |v'| == 0
      {
        var index: seq<nat> := [];
        assert is_subtree_index(index, u', u);
      }
      else
      {
        var index := iota(|v'|);
        assert is_subtree_index(index, u', u);
      }
    }
  }

  // The is_expansion relation must be reflexive
  lemma ExpansionReflexivityLemma(u: Node, depth: nat)
    ensures is_expansion(u, u, depth)
  {
  }

  // The is_expansion relation must be transitive
  lemma ExpansionTransitivityLemma(u: Node, v: Node, w: Node, depth: nat)
    requires is_expansion(u, v, depth)
    requires is_expansion(v, w, depth)
    ensures is_expansion(u, w, depth)
  {
  }

  // The depth of an expansion can be lowered
  lemma ExpansionDecreaseDepthLemma(u': Node, u: Node, depth: nat)
      requires is_expansion(u', u, depth)
      ensures forall d | 0 <= d <= depth :: is_expansion(u', u, d)
  {
  }    

  // Replacing a child v with an expansion v' preserves being an expansion
  lemma ExpansionReplaceChildLemma(u: Node, u': Node, v: Node, v': Node, i: nat, depth: nat)
    requires depth > 0
    requires 0 <= i < |u.children|
    requires v == u.children[i]
    requires is_expansion(v', v, depth - 1)
    requires u' == replace_child(u, i, v')
    ensures is_expansion(u', u, depth)
  {
    var v := u.children;
    var v' := u'.children;

    forall j | 0 <= j < |u.children| ensures is_expansion(v'[j], v[j], depth - 1)
    {
      if j == i
      {
      }
      else
      {
        assert v'[j] == v[j];
        ExpansionReflexivityLemma(v[j], depth - 1);
        assert is_expansion(v'[j], v[j], depth - 1);
      }
    }
  }  

  ghost predicate is_negamax_tt_result(value: bounded_int, u: Node, alpha: bounded_int, beta: bounded_int, depth: nat)
  {
    exists u': Node :: is_expansion(u', u, depth) && is_negamax_ab_result(value, u', alpha, beta)
  }

  ghost predicate is_valid_table_entry(t: TableEntry, u: Node)
  {
    (t.flag == Upperbound && exists u': Node :: is_expansion(u', u, t.depth) && t.value >= negamax(u')) ||
    (t.flag == Exact && exists u': Node :: is_expansion(u', u, t.depth) && t.value == negamax(u')) ||
    (t.flag == Lowerbound && exists u': Node :: is_expansion(u', u, t.depth) && t.value <= negamax(u'))
  }

  ghost predicate is_valid_table(T: TranspositionTable)
  {
    forall u | u in T.Keys :: is_valid_table_entry(T[u], u)
  }

  lemma NegamaxDepthLemma(u: Node, u': Node, alpha: bounded_int, beta: bounded_int, depth: nat)
      requires is_negamax_tt_result(negamax(u'), u', alpha, beta, depth)
      requires is_expansion(u', u, depth)
      ensures is_negamax_tt_result(negamax(u'), u, alpha, beta, depth)
  {
    assert is_negamax_tt_result(negamax(u'), u', alpha, beta, depth);
    var value := negamax(u');
    var u'' :| is_expansion(u'', u', depth) && is_negamax_ab_result(value, u'', alpha, beta);
    ExpansionTransitivityLemma(u'', u', u, depth);
    assert is_expansion(u'', u, depth);
  }

  lemma NegamaxDecreaseDepthLemma(value: bounded_int, u: Node, alpha: bounded_int, beta: bounded_int, depth: nat)
      requires is_negamax_tt_result(value, u, alpha, beta, depth)
      ensures forall d | 0 <= d <= depth :: is_negamax_tt_result(value, u, alpha, beta, d)
  {
    var u': Node :| is_expansion(u', u, depth) && is_negamax_ab_result(value, u', alpha, beta);
    ExpansionDecreaseDepthLemma(u', u, depth);
  }

  lemma TableLookupReturnLemma(u: Node, alpha: bounded_int, beta: bounded_int, depth: nat, t: TableEntry, T: TranspositionTable)
    requires is_valid_table(T)
    requires u in T.Keys
    requires t == T[u]
    requires t.depth >= depth
    requires alpha < beta
    requires (t.flag == Exact) ||
             (t.flag == Lowerbound && t.value >= beta) ||
             (t.flag == Upperbound && t.value <= alpha)
    ensures is_negamax_tt_result(t.value, u, alpha, beta, depth)
  {
    reveal is_negamax_ab_result();
    assert is_valid_table_entry(t, u);
    if t.flag == Exact 
    {
      var u': Node :| is_expansion(u', u, t.depth) && t.value == negamax(u');
      ExpansionDecreaseDepthLemma(u', u, t.depth);
      assert is_expansion(u', u, depth);
    }
    else if t.flag == Lowerbound && t.value >= beta
    {
      var u': Node :| is_expansion(u', u, t.depth) && t.value <= negamax(u');
      ExpansionDecreaseDepthLemma(u', u, t.depth);
      assert is_expansion(u', u, depth);
    }
    else if t.flag == Upperbound && t.value <= alpha
    {
      var u': Node :| is_expansion(u', u, t.depth) && t.value >= negamax(u');
      ExpansionDecreaseDepthLemma(u', u, t.depth);
      assert is_expansion(u', u, depth);
    }
  }

  lemma DepthZeroReturnLemma(u: Node, depth: nat, alpha0: bounded_int, beta0: bounded_int)
    requires depth == 0 || |u.children| == 0
    ensures is_negamax_tt_result(color(u) * u.eval, u, alpha0, beta0, depth)
  {
    reveal is_negamax_ab_result();
    ghost var u' := truncate_at_depth(u, 0);
    ghost var value := color(u) * u.eval;
    assert is_expansion(u', u, depth);
    assert is_negamax_ab_result(value, u', alpha0, beta0);
    assert is_negamax_tt_result(color(u) * u.eval, u', alpha0, beta0, 0);
  }

  lemma ApplyNegamaxLemma(v: seq<Node>, i: nat)
    requires 0 <= i < |v|
    ensures apply_negamax(v[..i+1]) == apply_negamax(v[..i]) + [negamax(v[i])]
  {}    

  lemma MinMaxLemma(u: Node, i: nat)
    requires 0 <= i < |u.children|
    requires partial_negamax(u, i) == -minimum'(apply_negamax(u.children[..i]))
    ensures partial_negamax(u, i + 1) == max(partial_negamax(u, i), -negamax(u.children[i]))
  {
    reveal partial_negamax();
    ApplyNegamaxLemma(u.children, i);
    var v := u.children[i];
    calc
    {
      partial_negamax(u, i+1);
      ==
      -minimum'(apply_negamax(u.children[..i+1]));
      ==
      -minimum'(apply_negamax(u.children[..i]) + [negamax(u.children[i])]);
      ==
      -minimum'(apply_negamax(u.children[..i]) + [negamax(v)]);
      ==
      -min(minimum'(apply_negamax(u.children[..i])), negamax(v));
      ==
      max(partial_negamax(u, i), -negamax(v));
    }
  }

  lemma TableUpdateLemma(value: bounded_int, u: Node, alpha0: bounded_int, beta0: bounded_int, depth: nat, T: TranspositionTable)
    requires alpha0 < beta0
    requires is_valid_table(T)
    requires is_negamax_tt_result(value, u, alpha0, beta0, depth)
    ensures value <= alpha0 ==> is_valid_table(T[u := TableEntry_(depth, value, Upperbound)])
    ensures alpha0 < value < beta0 ==> is_valid_table(T[u := TableEntry_(depth, value, Exact)])
    ensures value >= beta0 ==> is_valid_table(T[u := TableEntry_(depth, value, Lowerbound)])
  {
    reveal is_negamax_ab_result();
    var u': Node :| is_expansion(u', u, depth) && is_negamax_ab_result(value, u', alpha0, beta0);
  }
} // module NegamaxTTWCommonModule
