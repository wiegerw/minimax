// Copyright: Wieger Wesselink 2023
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)

include "negamax-ttw.dfy"

// Negamax with transposition table using current alpha for table updates
// https://en.wikipedia.org/wiki/Negamax

abstract module NegamaxTTWCurrentAlphaModule refines NegamaxTTWModule
{
  // The Wikipedia 2025 version of negamax with a transposition table with
  // one modification: the table update is done using the current value of alpha
  // instead of the original value.
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

      var i := 0;
      while i != |u.children|
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
        i := i + 1;
      }

      reveal is_negamax_ab_result();
      // N.B. The cases are not mutually exclusive. The upperbound case must be placed
      // after the lowerbound case. This is because after a break in the loop we want to
      // mark the result as a lowerbound.
      if value >= beta0   { T := T[u:=TableEntry_(depth,value,Lowerbound)]; }
      else if alpha < value < beta0 { T := T[u:=TableEntry_(depth,value,Exact)]; }
      else if value <= alpha   { T := T[u:=TableEntry_(depth,value,Upperbound)]; }
      return value;
    }
  }
}
