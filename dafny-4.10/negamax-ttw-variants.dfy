// Copyright: Wieger Wesselink 2023 - 2026
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)

include "negamax-ttw.dfy"

// This file contains three variations of NegamaxTTW, obtained by importing changes from NegamaxTTM.

// Change 1: Use the current alpha instead of the original alpha for table updates
abstract module NegamaxTTWCurrentAlphaModule refines NegamaxTTWModule
{
  class NegamaxTTWCurrentAlpha
  {
    var T: TranspositionTable  // Memoization table for previously computed positions

    // Negamax with transposition table: uses current alpha for more precise bounds
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

      // N.B. The cases are not mutually exclusive. The upperbound case must be placed
      // after the lowerbound case. This is because after a break in the loop we want to
      // mark the result as a lowerbound.
      TableUpdateCurrentAlphaLemma(value, u, alpha, alpha0, beta0, depth, T);
      if value >= beta0   { T := T[u:=TableEntry_(depth,value,Lowerbound)]; }
      else if alpha < value < beta0 { T := T[u:=TableEntry_(depth,value,Exact)]; }
      else if value <= alpha   { T := T[u:=TableEntry_(depth,value,Upperbound)]; }
      return value;
    }

    lemma TableUpdateCurrentAlphaLemma(value: bounded_int, u: Node, alpha: bounded_int, alpha0: bounded_int, beta0: bounded_int, depth: nat, T: TranspositionTable)
      requires alpha0 < beta0
      requires value <= alpha0 ==> alpha == alpha0
      requires turn_based()
      requires is_negamax_tt_result(value, u, alpha0, beta0, depth)
      requires is_valid_table(T)
      ensures value >= beta0 ==> is_valid_table(T[u := TableEntry_(depth, value, Lowerbound)])
      ensures !(value >= beta0) && alpha < value < beta0 ==> is_valid_table(T[u := TableEntry_(depth, value, Exact)])
      ensures !(value >= beta0) && value <= alpha ==> is_valid_table(T[u := TableEntry_(depth, value, Upperbound)])
    {
      reveal is_negamax_ab_result();
      var u': Node :| is_expansion(u', u, depth) && is_negamax_ab_result(value, u', alpha0, beta0);
    }
  }
}

// Change 2: Put an extra condition on the table updates
abstract module NegamaxTTWExtraDepthConditionModule refines NegamaxTTWModule
{
  class NegamaxTTWExtraDepthCondition
  {
    var T: TranspositionTable  // Memoization table for previously computed positions

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
      if u !in T.Keys || T[u].depth <= depth  // extra condition
      {
        if value <= alpha0      {T := T[u:=TableEntry_(depth,value,Upperbound)];}
        else if alpha0 < value < beta0 {T:=T[u:=TableEntry_(depth,value,Exact)];}
        else if value >= beta0  {T := T[u:=TableEntry_(depth,value,Lowerbound)];}
      }
        return value;
    }
  }
}

// Change 3: Use the Fishburn propagation variant of alpha-beta
abstract module NegamaxTTWFishburnPropagationModule refines NegamaxTTWCommonModule
{
  class NegamaxTTWFishburnPropagation
  {
    var T: TranspositionTable  // Memoization table for previously computed positions

    // Negamax with transposition table: uses Fishburn's value propagation method
    method Negamax(u: Node, alpha: bounded_int, beta: bounded_int, depth:nat)
      returns (result: bounded_int)
      modifies this`T
      requires alpha < beta
      requires turn_based()
      requires is_valid_table(T)
      ensures is_negamax_tt_result(result, u, alpha, beta, depth)
      ensures is_valid_table(T)
    {
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
        DepthZeroReturnLemma(u, depth, alpha, beta);
        return color(u) * u.eval;
      }
      var value: bounded_int := -INFINITY;
      for i := 0 to |u.children|
        invariant is_valid_table(T)
        invariant 0 <= i <= |u.children|
        invariant i == 0 ==> value == -INFINITY
        invariant alpha < beta
        invariant value < beta
        invariant i > 0 ==> exists u': Node :: is_expansion(u', u, depth) && is_partial_negamax_ab_result(value, u', i, alpha, beta)
        invariant i == |u.children| ==> is_negamax_tt_result(value, u, alpha, beta, depth)
      {
        ghost var old_alpha := alpha;
        ghost var old_value := value;
        var v := u.children[i];
        var negamax_v := Negamax(v, -beta, -max(value, alpha), depth - 1);
        value := max(value, -negamax_v);
        if value >= beta
        {
          LoopBreakLemma(u, v, i, depth, alpha, beta, old_alpha, old_value, value, negamax_v);
          break;
        }
        LoopMaintenanceLemma(u, v, i, depth, alpha, beta, old_alpha, old_value, value, negamax_v);
      }
      TableUpdateLemma(value, u, alpha, beta, depth, T);
      if value <= alpha 
      {
        T := T[u:=TableEntry_(depth,value,Upperbound)];
      }
      else if alpha < value < beta
      {
        T := T[u:=TableEntry_(depth,value,Exact)];
      }
      else if value >= beta
      {
        T := T[u:=TableEntry_(depth,value,Lowerbound)];
      }
      return value;
    }
  }

  lemma LoopBreakLemma2(u: Node, u': Node, v: Node, v': Node, i: nat, depth: nat, alpha: bounded_int, beta: bounded_int, old_alpha: bounded_int, old_value: bounded_int, value: bounded_int, negamax_v: bounded_int)
    requires turn_based()
    requires 0 <= i < |u.children|
    requires |u.children| == |u'.children|
    requires u' == replace_child(u, i, v')
    requires alpha < beta
    requires old_value < beta
    requires value == max(old_value, -negamax_v)
    requires value >= beta
    requires is_negamax_ab_result(negamax_v, v', -beta, -max(old_value, alpha))
    ensures is_negamax_ab_result(value, u', alpha, beta)
  {
    reveal is_negamax_ab_result();
    reveal partial_negamax();
    MinMaxLemma(u', i);
    assert partial_negamax(u', i + 1) == max(partial_negamax(u', i), -negamax(u'.children[i]));
    assert value <= negamax(u');
  }

  lemma LoopBreakLemma(u: Node, v: Node, i: nat, depth: nat, alpha: bounded_int, beta: bounded_int, old_alpha: bounded_int, old_value: bounded_int, value: bounded_int, negamax_v: bounded_int)
    requires turn_based()
    requires 0 <= i < |u.children|
    requires depth > 0
    requires v == u.children[i]
    requires alpha < beta
    requires old_value < beta
    requires value == max(old_value, -negamax_v)
    requires value >= beta
    requires is_negamax_tt_result(negamax_v, v, -beta, -max(old_value, alpha), depth - 1)
    requires i == 0 ==> old_value == -INFINITY
    requires i > 0 ==> exists u': Node :: is_expansion(u', u, depth) && is_partial_negamax_ab_result(old_value, u', i, alpha, beta)
    ensures is_negamax_tt_result(value, u, alpha, beta, depth)
  {
    var v': Node :|
      is_expansion(v', v, depth - 1) &&
      is_negamax_ab_result(negamax_v, v', -beta, -max(old_value, alpha));

    if i > 0 
    {
      var u': Node :|
        is_expansion(u', u, depth) &&
        is_partial_negamax_ab_result(old_value, u', i, alpha, beta);
  
      var u'' := replace_child(u', i, v');
      assert is_expansion(u'', u, depth);

      LoopBreakLemma2(u', u'', v, v', i, depth, alpha, beta, old_alpha, old_value, value, negamax_v);
      assert is_negamax_ab_result(value, u'', alpha, beta);
    }
    else
    {
      reveal partial_negamax();
      var u' := replace_child(u, i, v');

      LoopBreakLemma2(u, u', v, v', i, depth, alpha, beta, old_alpha, old_value, value, negamax_v);
      assert is_negamax_ab_result(value, u', alpha, beta);

      ExpansionReplaceChildLemma(u, u', v, v', i, depth);
      assert is_expansion(u', u, depth);

      assert is_negamax_ab_result(value, u', alpha, beta);
    }
  }

  lemma LoopMaintenanceLemma2(u': Node, u'': Node, v: Node, v': Node, i: nat, depth: nat, alpha: bounded_int, beta: bounded_int, old_alpha: bounded_int, old_value: bounded_int, value: bounded_int, negamax_v: bounded_int)
    requires 0 <= i < |u'.children|
    requires |u'.children| == |u''.children|
    requires u'' == replace_child(u', i, v')
    requires alpha < beta
    requires old_value < beta
    requires value == max(old_value, -negamax_v)
    requires value < beta
    requires is_negamax_ab_result(negamax_v, v', -beta, -max(old_value, alpha))
    requires is_partial_negamax_ab_result(old_value, u', i, alpha, beta)
    ensures is_partial_negamax_ab_result(value, u'', i + 1, alpha, beta)
  {
    reveal is_negamax_ab_result();
    reveal partial_negamax();  
    MinMaxLemma(u'', i);
    assert partial_negamax(u'', i + 1) == max(partial_negamax(u'', i), -negamax(u''.children[i]));
    assert partial_negamax(u'', i + 1) == max(partial_negamax(u'', i), -negamax(v'));
    assert partial_negamax(u'', i + 1) < beta;
    assert value < beta;
  }

  lemma LoopMaintenanceLemma(u: Node, v: Node, i: nat, depth: nat, alpha: bounded_int, beta: bounded_int, old_alpha: bounded_int, old_value: bounded_int, value: bounded_int, negamax_v: bounded_int)
    requires turn_based()
    requires 0 <= i < |u.children|
    requires depth > 0
    requires v == u.children[i]
    requires alpha < beta
    requires old_value < beta
    requires value == max(old_value, -negamax_v)
    requires value < beta
    requires is_negamax_tt_result(negamax_v, v, -beta, -max(old_value, alpha), depth - 1)
    requires i == 0 ==> old_value == -INFINITY && old_alpha == alpha
    requires i > 0 ==>
      exists u': Node :: 
        is_expansion(u', u, depth) &&
        is_partial_negamax_ab_result(old_value, u', i, alpha, beta)
    ensures
      exists u': Node :: 
        is_expansion(u', u, depth) &&
        is_partial_negamax_ab_result(value, u', i + 1, alpha, beta)
    ensures i == |u.children| - 1 ==> is_negamax_tt_result(value, u, alpha, beta, depth)
  {
    reveal is_negamax_ab_result();

    var v': Node :|
      is_expansion(v', v, depth - 1) &&
      is_negamax_ab_result(negamax_v, v', -beta, -max(old_value, alpha));

    if i > 0
    {
      var u': Node :|
        is_expansion(u', u, depth) &&
        is_partial_negamax_ab_result(old_value, u', i, alpha, beta);

      var u'' := replace_child(u', i, v');
      assert is_expansion(u'', u, depth);

      LoopMaintenanceLemma2(u', u'', v, v', i, depth, alpha, beta, old_alpha, old_value, value, negamax_v);

      if i == |u.children| - 1
      {
        assert is_partial_negamax_ab_result(value, u'', i + 1, alpha, beta);
        PartialNegamaxAlphaBetaLemma(value, u'', i + 1, alpha, beta);
        assert is_negamax_ab_result(value, u'', alpha, beta);
      }
    }
    else
    {
      reveal partial_negamax();
      var u' := replace_child(u, i, v');
      ExpansionReplaceChildLemma(u, u', v, v', i, depth);
      assert is_expansion(u', u, depth);

      LoopMaintenanceLemma2(u, u', v, v', i, depth, alpha, beta, old_alpha, old_value, value, negamax_v);
      if i == |u.children| - 1
      {
        assert is_partial_negamax_ab_result(value, u', i + 1, alpha, beta);
        PartialNegamaxAlphaBetaLemma(value, u', i + 1, alpha, beta);
        assert is_negamax_ab_result(value, u', alpha, beta);
      }
    }
  }

} // module NegamaxTTWFishburnPropagationModule
