// Copyright: Wieger Wesselink 2026
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)

include "definitions.dfy"
include "lemmas.dfy"

// Implementation of the MT-SSS* / negamax-Plaat algorithm from the paper
// "Best-first Fixed-depth Minimax algorithms" by Plaat et al. (1996).

abstract module NegamaxPlaat1996Module
{
  import opened Definitions
  import opened Lemmas

  ghost predicate is_negamax_tt_result(value: bounded_int, u: Node, alpha: bounded_int, beta: bounded_int)
  {
    is_negamax_ab_result(value, u, alpha, beta)
  }

  datatype PlaatTableEntry = PlaatTableEntry_(lowerbound: bounded_int, upperbound: bounded_int)
  type PlaatTranspositionTable = map<Node, PlaatTableEntry>

  ghost predicate is_valid_table_entry(t: PlaatTableEntry, u: Node)
  {
    (t.upperbound < INFINITY ==> t.upperbound >= negamax(u)) &&
    (t.lowerbound > -INFINITY ==> t.lowerbound <= negamax(u))
  }

  ghost predicate is_valid_table(T: PlaatTranspositionTable)
  {
    forall u | u in T.Keys :: is_valid_table_entry(T[u], u)
  }

  lemma TableLookupReturnLemma(u: Node, alpha: bounded_int, beta: bounded_int, t: PlaatTableEntry, T: PlaatTranspositionTable)
    requires is_valid_table(T)
    requires u in T.Keys
    requires t == T[u]
    requires alpha < beta
    requires (t.lowerbound >= beta) || (t.upperbound <= alpha)
    ensures t.lowerbound >= beta ==> is_negamax_tt_result(t.lowerbound, u, alpha, beta)
    ensures t.upperbound <= alpha ==> is_negamax_tt_result(t.upperbound, u, alpha, beta)
  {
    reveal is_negamax_ab_result();
    if t.lowerbound >= beta
    {
      assert t.lowerbound > -INFINITY;
    }
    if t.upperbound <= alpha
    {
      assert t.upperbound < INFINITY;
    }
  }

  lemma TableUpdateLemma(result: bounded_int, u: Node, alpha0: bounded_int, beta0: bounded_int, T: PlaatTranspositionTable)
    requires alpha0 < beta0
    requires is_valid_table(T)
    requires is_negamax_tt_result(result, u, alpha0, beta0)
    ensures
      var t := if u in T then T[u] else PlaatTableEntry_(-INFINITY, INFINITY);
      var lower := if result > alpha0 then result else t.lowerbound;
      var upper := if result < beta0 then result else t.upperbound;
      is_valid_table(T[u := PlaatTableEntry_(lower, upper)])
  {
    reveal is_negamax_ab_result();
  }

  class NegamaxPlaat1996Algorithm
  {
    var T: PlaatTranspositionTable

    // Implementation of the MT-SSS* / negamax version of Plaat et al. 1996.
    method Negamax(u: Node, alpha0: bounded_int, beta0: bounded_int) returns (result: bounded_int)
      requires turn_based()
      requires alpha0 < beta0
      requires is_valid_table(T)
      modifies this`T
      ensures is_negamax_tt_result(result, u, alpha0, beta0)
      ensures is_valid_table(T)
      decreases u
    {
      reveal partial_negamax();
      reveal is_negamax_ab_result();

      var alpha := alpha0;
      var beta := beta0;

      // Check if position is in the transposition table
      if u in T
      {
        var t := T[u];
        if t.lowerbound >= beta
        {
          TableLookupReturnLemma(u, alpha, beta, t, T);
          return t.lowerbound;
        }
        if t.upperbound <= alpha
        {
          TableLookupReturnLemma(u, alpha, beta, t, T);
          return t.upperbound;
        }
      }

      if |u.children| == 0
      {
        NoChildrenReturnLemma(u, alpha0, beta0);
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
          invariant i > 0 ==> is_partial_negamax_ab_result(value, u, i, alpha0, beta0)
          invariant i == |u.children| ==> is_negamax_tt_result(value, u, alpha0, beta0)
        {
          ghost var old_alpha := alpha;
          ghost var old_value := value;

          var v := u.children[i];
          var negamax_v := Negamax(v, -beta0, -alpha);
          value := max(value, -negamax_v);
          alpha := max(alpha, value);

          if alpha >= beta0
          {
            LoopBreakLemma(u, v, i, alpha0, beta0, old_alpha, old_value, alpha, value, negamax_v);
            break;
          }
          LoopMaintenanceLemma(u, v, i, alpha0, beta0, old_alpha, old_value, alpha, value, negamax_v);
        }
        result := value;
      }

      assert result > alpha0 || result < beta0;

      // Update the transposition table
      TableUpdateLemma(result, u, alpha0, beta0, T);
      var t := if u in T then T[u] else PlaatTableEntry_(-INFINITY, INFINITY);
      var lower := if result > alpha0 then result else t.lowerbound;
      var upper := if result < beta0 then result else t.upperbound;
      T := T[u := PlaatTableEntry_(lower, upper)];

      return result;
    }
  }

  lemma NoChildrenReturnLemma(u: Node, alpha0: bounded_int, beta0: bounded_int)
    requires |u.children| == 0
    ensures is_negamax_tt_result(color(u) * u.eval, u, alpha0, beta0)
  {
    reveal is_negamax_ab_result();
  }

  lemma LoopBreakLemma(u: Node, v: Node, i: nat, alpha0: bounded_int, beta0: bounded_int, old_alpha: bounded_int, old_value: bounded_int, alpha: bounded_int, value: bounded_int, negamax_v: bounded_int)
    requires turn_based()
    requires 0 <= i < |u.children|
    requires v == u.children[i]
    requires alpha >= beta0
    requires alpha0 <= old_alpha < beta0
    requires value == max(old_value, -negamax_v)
    requires alpha == max(old_alpha, value)
    requires is_negamax_tt_result(negamax_v, v, -beta0, -old_alpha)
    requires i == 0 ==> old_value == -INFINITY && old_alpha == alpha0
    requires i > 0 ==> is_partial_negamax_ab_result(old_value, u, i, alpha0, beta0)
    ensures is_negamax_tt_result(value, u, alpha0, beta0)
  {
    reveal partial_negamax();
    reveal is_negamax_ab_result();

    ChildrenAppendLemma(u, i);
    PartialNegamaxLemma(u);
  }

  lemma LoopMaintenanceLemma(u: Node, v: Node, i: nat, alpha0: bounded_int, beta0: bounded_int, old_alpha: bounded_int, old_value: bounded_int, alpha: bounded_int, value: bounded_int, negamax_v: bounded_int)
    requires turn_based()
    requires 0 <= i < |u.children|
    requires v == u.children[i]
    requires alpha0 <= old_alpha < beta0
    requires old_value <= alpha0 ==> old_alpha == alpha0
    requires alpha < beta0
    requires alpha0 < old_value < beta0 ==> old_alpha == old_value
    requires value == max(old_value, -negamax_v)
    requires alpha == max(old_alpha, value)
    requires is_negamax_tt_result(negamax_v, v, -beta0, -old_alpha)
    requires i == 0 ==> old_value == -INFINITY && old_alpha == alpha0
    requires i > 0 ==> is_partial_negamax_ab_result(old_value, u, i, alpha0, beta0)
    ensures is_partial_negamax_ab_result(value, u, i + 1, alpha0, beta0)
    ensures i == |u.children| - 1 ==> is_negamax_tt_result(value, u, alpha0, beta0)
  {
    reveal partial_negamax();
    reveal is_negamax_ab_result();

    ChildrenAppendLemma(u, i);
    if i == |u.children| - 1
    {
      PartialNegamaxLemma(u);
    }
  }

} // module NegamaxPlaat1996Module
