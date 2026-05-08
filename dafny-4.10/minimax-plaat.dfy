// Copyright: Wieger Wesselink 2026
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)

include "definitions.dfy"
include "lemmas.dfy"

// Implementation of the MT-SSS* / minimax-Plaat algorithm from the paper
// "Best-first Fixed-depth Minimax algorithms" by Plaat et al. (1996).

abstract module MinimaxPlaat1996Module
{
  import opened Definitions
  import opened Lemmas

  datatype PlaatTableEntry = PlaatTableEntry_(lowerbound: bounded_int, upperbound: bounded_int)
  type PlaatTranspositionTable = map<Node, PlaatTableEntry>

  ghost predicate is_valid_table_entry(t: PlaatTableEntry, u: Node)
  {
    (t.upperbound < INFINITY ==> t.upperbound >= minimax(u)) &&
    (t.lowerbound > -INFINITY ==> t.lowerbound <= minimax(u))
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
    ensures t.lowerbound >= beta ==> is_minimax_ab_result(t.lowerbound, u, alpha, beta)
    ensures t.upperbound <= alpha ==> is_minimax_ab_result(t.upperbound, u, alpha, beta)
  {
    reveal is_minimax_ab_result();
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
    requires is_minimax_ab_result(result, u, alpha0, beta0)
    ensures
      var t := if u in T then T[u] else PlaatTableEntry_(-INFINITY, INFINITY);
      var lower := if result > alpha0 then result else t.lowerbound;
      var upper := if result < beta0 then result else t.upperbound;
      is_valid_table(T[u := PlaatTableEntry_(lower, upper)])
  {
    reveal is_minimax_ab_result();
  }

  class MinimaxPlaat1996Algorithm
  {
    var T: PlaatTranspositionTable

    // Implementation of the MT-SSS* / minimax version of Plaat et al. 1996.
    method Minimax(u: Node, alpha0: bounded_int, beta0: bounded_int) returns (result: bounded_int)
      requires turn_based()
      requires alpha0 < beta0
      requires is_valid_table(T)
      modifies this`T
      ensures is_minimax_ab_result(result, u, alpha0, beta0)
      ensures is_valid_table(T)
      decreases u
    {
      reveal partial_minimax();
      reveal is_minimax_ab_result();

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
        result := u.eval;
      }
      else if u.color == Black
      {
        var value: bounded_int := INFINITY;

        for i := 0 to |u.children|
          invariant turn_based()
          invariant is_valid_table(T)
          invariant 0 <= i <= |u.children|
          invariant alpha0 < beta <= beta0
          invariant value >= beta0 ==> beta == beta0
          invariant alpha0 < value < beta0 ==> value == beta
          invariant i == 0 ==> value == INFINITY && beta == beta0
          invariant i > 0 ==> is_partial_minimax_ab_result(value, u, i, alpha0, beta0)
          invariant i == |u.children| ==> is_minimax_ab_result(value, u, alpha0, beta0)
        {
          ghost var old_beta := beta;
          ghost var old_value := value;

          var v := u.children[i];
          var minimax_v := Minimax(v, alpha0, beta);
          value := min(value, minimax_v);
          beta := min(beta, value);

          if beta <= alpha0
          {
            LoopBreakBlackLemma(u, v, i, alpha0, beta0, old_beta, old_value, beta, value, minimax_v);
            break;
          }
          LoopMaintenanceBlackLemma(u, v, i, alpha0, beta0, old_beta, old_value, beta, value, minimax_v);
        }
        result := value;
      }
      else // if u.color == White
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
          invariant i > 0 ==> is_partial_minimax_ab_result(value, u, i, alpha0, beta0)
          invariant i == |u.children| ==> is_minimax_ab_result(value, u, alpha0, beta0)
        {
          ghost var old_alpha := alpha;
          ghost var old_value := value;

          var v := u.children[i];
          var minimax_v := Minimax(v, alpha, beta0);
          value := max(value, minimax_v);
          alpha := max(alpha, value);

          if alpha >= beta0
          {
            LoopBreakWhiteLemma(u, v, i, alpha0, beta0, old_alpha, old_value, alpha, value, minimax_v);
            break;
          }
          LoopMaintenanceWhiteLemma(u, v, i, alpha0, beta0, old_alpha, old_value, alpha, value, minimax_v);
        }
        result := value;
      }

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
    ensures is_minimax_ab_result(u.eval, u, alpha0, beta0)
  {
    reveal is_minimax_ab_result();
  }

  lemma LoopBreakBlackLemma(u: Node, v: Node, i: nat, alpha0: bounded_int, beta0: bounded_int, old_beta: bounded_int, old_value: bounded_int, beta: bounded_int, value: bounded_int, minimax_v: bounded_int)
    requires turn_based()
    requires u.color == Black
    requires 0 <= i < |u.children|
    requires v == u.children[i]
    requires beta <= alpha0
    requires alpha0 < old_beta <= beta0
    requires value == min(old_value, minimax_v)
    requires beta == min(old_beta, value)
    requires is_minimax_ab_result(minimax_v, v, alpha0, old_beta)
    requires i == 0 ==> old_value == INFINITY && old_beta == beta0
    requires i > 0 ==> is_partial_minimax_ab_result(old_value, u, i, alpha0, beta0)
    ensures is_minimax_ab_result(value, u, alpha0, beta0)
  {
    reveal partial_minimax();
    reveal is_minimax_ab_result();
    ChildrenAppendLemma(u, i);
    PartialMinimaxLemma(u);
  }

  lemma LoopMaintenanceBlackLemma(u: Node, v: Node, i: nat, alpha0: bounded_int, beta0: bounded_int, old_beta: bounded_int, old_value: bounded_int, beta: bounded_int, value: bounded_int, minimax_v: bounded_int)
    requires turn_based()
    requires u.color == Black
    requires 0 <= i < |u.children|
    requires v == u.children[i]
    requires alpha0 < old_beta <= beta0
    requires old_value >= beta0 ==> old_beta == beta0
    requires beta > alpha0
    requires alpha0 < old_value < beta0 ==> old_beta == old_value
    requires value == min(old_value, minimax_v)
    requires beta == min(old_beta, value)
    requires is_minimax_ab_result(minimax_v, v, alpha0, old_beta)
    requires i == 0 ==> old_value == INFINITY && old_beta == beta0
    requires i > 0 ==> is_partial_minimax_ab_result(old_value, u, i, alpha0, beta0)
    ensures is_partial_minimax_ab_result(value, u, i + 1, alpha0, beta0)
    ensures i == |u.children| - 1 ==> is_minimax_ab_result(value, u, alpha0, beta0)
  {
    reveal partial_minimax();
    reveal is_minimax_ab_result();
    ChildrenAppendLemma(u, i);
    MinimaxMinMaxLemma(u, i);
  }

  lemma LoopBreakWhiteLemma(u: Node, v: Node, i: nat, alpha0: bounded_int, beta0: bounded_int, old_alpha: bounded_int, old_value: bounded_int, alpha: bounded_int, value: bounded_int, minimax_v: bounded_int)
    requires turn_based()
    requires u.color == White
    requires 0 <= i < |u.children|
    requires v == u.children[i]
    requires alpha >= beta0
    requires alpha0 <= old_alpha < beta0
    requires value == max(old_value, minimax_v)
    requires alpha == max(old_alpha, value)
    requires is_minimax_ab_result(minimax_v, v, old_alpha, beta0)
    requires i == 0 ==> old_value == -INFINITY && old_alpha == alpha0
    requires i > 0 ==> is_partial_minimax_ab_result(old_value, u, i, alpha0, beta0)
    ensures is_minimax_ab_result(value, u, alpha0, beta0)
  {
    reveal partial_minimax();
    reveal is_minimax_ab_result();
    ChildrenAppendLemma(u, i);
    PartialMinimaxLemma(u);
  }

  lemma LoopMaintenanceWhiteLemma(u: Node, v: Node, i: nat, alpha0: bounded_int, beta0: bounded_int, old_alpha: bounded_int, old_value: bounded_int, alpha: bounded_int, value: bounded_int, minimax_v: bounded_int)
    requires turn_based()
    requires u.color == White
    requires 0 <= i < |u.children|
    requires v == u.children[i]
    requires alpha0 <= old_alpha < beta0
    requires old_value <= alpha0 ==> old_alpha == alpha0
    requires alpha < beta0
    requires alpha0 < old_value < beta0 ==> old_alpha == old_value
    requires value == max(old_value, minimax_v)
    requires alpha == max(old_alpha, value)
    requires is_minimax_ab_result(minimax_v, v, old_alpha, beta0)
    requires i == 0 ==> old_value == -INFINITY && old_alpha == alpha0
    requires i > 0 ==> is_partial_minimax_ab_result(old_value, u, i, alpha0, beta0)
    ensures is_partial_minimax_ab_result(value, u, i + 1, alpha0, beta0)
    ensures i == |u.children| - 1 ==> is_minimax_ab_result(value, u, alpha0, beta0)
  {
    reveal partial_minimax();
    reveal is_minimax_ab_result();
    ChildrenAppendLemma(u, i);
    MinimaxMinMaxLemma(u, i);
  }

} // module MinimaxPlaat1996Module
