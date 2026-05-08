// Copyright: Wieger Wesselink 2026
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)

include "definitions.dfy"
include "lemmas.dfy"

// Implementation of the depth-limited MT-SSS* / negamax-Plaat algorithm from the paper
// "Best-first Fixed-depth Minimax algorithms" by Plaat et al. (1996).

abstract module NegamaxDepthPlaat1996Module
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

  datatype PlaatTableEntry = PlaatTableEntry_(lowerbound: bounded_int, upperbound: bounded_int, depth: nat)
  type PlaatTranspositionTable = map<Node, PlaatTableEntry>

  ghost predicate is_valid_table_entry(t: PlaatTableEntry, u: Node)
  {
    (t.upperbound < INFINITY ==> exists u': Node :: is_expansion(u', u, t.depth) && t.upperbound >= negamax(u')) &&
    (t.lowerbound > -INFINITY ==> exists u': Node :: is_expansion(u', u, t.depth) && t.lowerbound <= negamax(u'))
  }

  ghost predicate is_valid_table(T: PlaatTranspositionTable)
  {
    forall u | u in T.Keys :: is_valid_table_entry(T[u], u)
  }

  lemma TableLookupReturnLemma(u: Node, alpha: bounded_int, beta: bounded_int, depth: nat, t: PlaatTableEntry, T: PlaatTranspositionTable)
    requires is_valid_table(T)
    requires u in T.Keys
    requires t == T[u]
    requires t.depth >= depth
    requires alpha < beta
    ensures t.lowerbound >= beta ==> is_negamax_tt_result(t.lowerbound, u, alpha, beta, depth)
    ensures t.upperbound <= alpha ==> is_negamax_tt_result(t.upperbound, u, alpha, beta, depth)
  {
    reveal is_negamax_ab_result();
    if t.lowerbound >= beta
    {
      assert t.lowerbound > -INFINITY;
      var u': Node :| is_expansion(u', u, t.depth) && t.lowerbound <= negamax(u');
      ExpansionDecreaseDepthLemma(u', u, t.depth);
      assert is_expansion(u', u, depth);
    }
    if t.upperbound <= alpha
    {
      assert t.upperbound < INFINITY;
      var u': Node :| is_expansion(u', u, t.depth) && t.upperbound >= negamax(u');
      ExpansionDecreaseDepthLemma(u', u, t.depth);
      assert is_expansion(u', u, depth);
    }
  }

  lemma TableUpdateLemma(result: bounded_int, u: Node, alpha0: bounded_int, beta0: bounded_int, depth: nat, T: PlaatTranspositionTable)
    requires alpha0 < beta0
    requires is_valid_table(T)
    requires is_negamax_tt_result(result, u, alpha0, beta0, depth)
    ensures
      var lower := if result > alpha0 then result else -INFINITY;
      var upper := if result < beta0 then result else INFINITY;
      is_valid_table(T[u := PlaatTableEntry_(lower, upper, depth)])
  {
    reveal is_negamax_ab_result();
  }

  class NegamaxDepthPlaat1996Algorithm
  {
    var T: PlaatTranspositionTable

    // Implementation of the depth-limited MT-SSS* / negamax version of Plaat et al. 1996.
    method Negamax(u: Node, alpha0: bounded_int, beta0: bounded_int, depth: nat) returns (result: bounded_int)
      requires turn_based()
      requires alpha0 < beta0
      requires is_valid_table(T)
      modifies this`T
      ensures is_negamax_tt_result(result, u, alpha0, beta0, depth)
      ensures is_valid_table(T)
      decreases depth, u
    {
      var alpha := alpha0;
      var beta := beta0;

      // Check if position is in the transposition table
      if u in T
      {
        var t := T[u];
        if t.depth >= depth
        {
          TableLookupReturnLemma(u, alpha, beta, depth, t, T);
          if t.lowerbound >= beta
          {
            return t.lowerbound;
          }
          if t.upperbound <= alpha
          {
            return t.upperbound;
          }
        }
      }

      if depth == 0 || |u.children| == 0
      {
        DepthZeroReturnLemma(u, depth, alpha0, beta0);
        result := color(u) * u.eval;
      }
      else
      {
        var value: bounded_int := -INFINITY;

        for i := 0 to |u.children|
          invariant turn_based()
          invariant is_valid_table(T)
          invariant 0 <= i <= |u.children|
          invariant alpha0 <= alpha < beta0
          invariant value <= alpha0 ==> alpha == alpha0
          invariant alpha0 < value < beta0 ==> value == alpha
          invariant i == 0 ==> value == -INFINITY && alpha == alpha0
          invariant i > 0 ==> exists u': Node :: is_expansion(u', u, depth) && is_partial_negamax_ab_result(value, u', i, alpha0, beta0)
          invariant i == |u.children| ==> is_negamax_tt_result(value, u, alpha0, beta0, depth)
        {
          ghost var old_alpha := alpha;
          ghost var old_value := value;

          var v := u.children[i];
          var negamax_v := Negamax(v, -beta0, -alpha, depth - 1);
          value := max(value, -negamax_v);
          alpha := max(alpha, value);

          if alpha >= beta0
          {
            LoopBreakLemma(u, v, i, depth, alpha0, beta0, old_alpha, old_value, alpha, value, negamax_v);
            break;
          }
          LoopMaintenanceLemma(u, v, i, depth, alpha0, beta0, old_alpha, old_value, alpha, value, negamax_v);
        }
        result := value;
      }

      // Update the transposition table
      TableUpdateLemma(result, u, alpha0, beta0, depth, T);
      var lower := -INFINITY;
      var upper := INFINITY;
      if result > alpha0
      {
        lower := result;
      }
      if result < beta0
      {
        upper := result;
      }
      T := T[u := PlaatTableEntry_(lower, upper, depth)];

      return result;
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
  }

  lemma LoopBreakHelperLemma(u: Node, u': Node, v: Node, v': Node, i: nat, depth: nat, alpha0: bounded_int, beta0: bounded_int, old_alpha: bounded_int, old_value: bounded_int, alpha: bounded_int, value: bounded_int, negamax_v: bounded_int)
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
    NegamaxMinMaxLemma(u', i);
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
    requires i > 0 ==> exists u': Node :: is_expansion(u', u, depth) && is_partial_negamax_ab_result(old_value, u', i, alpha0, beta0)
    ensures is_negamax_tt_result(value, u, alpha0, beta0, depth)
  {
    var v': Node :| is_expansion(v', v, depth - 1) && is_negamax_ab_result(negamax_v, v', -beta0, -old_alpha);

    if i > 0 
    {
      var u': Node :| is_expansion(u', u, depth) && is_partial_negamax_ab_result(old_value, u', i, alpha0, beta0);
      var u'' := replace_child(u', i, v');
      LoopBreakHelperLemma(u', u'', v, v', i, depth, alpha0, beta0, old_alpha, old_value, alpha, value, negamax_v);
    }
    else
    {
      reveal partial_negamax();
      var u' := replace_child(u, i, v');
      ExpansionReplaceChildLemma(u, u', v, v', i, depth);
      LoopBreakHelperLemma(u, u', v, v', i, depth, alpha0, beta0, old_alpha, old_value, alpha, value, negamax_v);
    }
  }

  lemma LoopMaintenanceHelperLemma(u': Node, u'': Node, v: Node, v': Node, i: nat, depth: nat, alpha0: bounded_int, beta0: bounded_int, old_alpha: bounded_int, old_value: bounded_int, alpha: bounded_int, value: bounded_int, negamax_v: bounded_int)
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
    NegamaxMinMaxLemma(u'', i);
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
    requires i > 0 ==> exists u': Node :: is_expansion(u', u, depth) && is_partial_negamax_ab_result(old_value, u', i, alpha0, beta0)
    ensures exists u': Node :: is_expansion(u', u, depth) && is_partial_negamax_ab_result(value, u', i + 1, alpha0, beta0)
    ensures i == |u.children| - 1 ==> is_negamax_tt_result(value, u, alpha0, beta0, depth)
  {
    reveal is_negamax_ab_result();

    var v': Node :| is_expansion(v', v, depth - 1) && is_negamax_ab_result(negamax_v, v', -beta0, -old_alpha);

    if i > 0
    {
      var u': Node :| is_expansion(u', u, depth) && is_partial_negamax_ab_result(old_value, u', i, alpha0, beta0);
      var u'' := replace_child(u', i, v');
      assert is_expansion(u'', u, depth);
      LoopMaintenanceHelperLemma(u', u'', v, v', i, depth, alpha0, beta0, old_alpha, old_value, alpha, value, negamax_v);

      if i == |u.children| - 1
      {
        assert is_partial_negamax_ab_result(value, u'', i + 1, alpha0, beta0);
        PartialNegamaxAlphaBetaLemma(value, u'', i + 1, alpha0, beta0);
      }
    }
    else
    {
      reveal partial_negamax();
      var u' := replace_child(u, i, v');
      ExpansionReplaceChildLemma(u, u', v, v', i, depth);
      LoopMaintenanceHelperLemma(u, u', v, v', i, depth, alpha0, beta0, old_alpha, old_value, alpha, value, negamax_v);
      if i == |u.children| - 1
      {
        PartialNegamaxAlphaBetaLemma(value, u', i + 1, alpha0, beta0);
      }
    }
  }
} // module NegamaxDepthPlaat1996Module
