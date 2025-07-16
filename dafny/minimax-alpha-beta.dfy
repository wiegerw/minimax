// Copyright: Wieger Wesselink 2023
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)

include "definitions.dfy"
include "lemmas.dfy"

// Minimax with alpha-beta pruning for efficient game tree search
// https://en.wikipedia.org/wiki/Negamax

// Based on Knuth 1975 (fail-hard)
abstract module MinimaxKnuth1975Module
{
  import opened Definitions
  import opened Lemmas

  class MinimaxABKnuth1975Algorithm
  {
    // Minimax with alpha-beta pruning: prunes branches that cannot affect result
    method Minimax(u: Node, alpha: bounded_int, beta: bounded_int) returns (result: bounded_int)
      requires alpha < beta
      ensures is_minimax_ab_result(result, u, alpha, beta)
    {
      if |u.children| == 0
      {
        return u.eval;
      }
      else if u.color == Black
      {
        var value: bounded_int := beta;

        for i := 0 to |u.children|
          invariant 0 <= i <= |u.children|
          invariant value <= beta
          invariant is_partial_minimax_ab_result(value, u, i, alpha, beta)
          invariant i == |u.children| ==> is_minimax_ab_result(value, u, alpha, beta)
        {
          ghost var old_value := value;

          var v := u.children[i];
          var minimax_v := Minimax(v, alpha, beta);

          value := min(value, minimax_v);
          if value <= alpha
          {
            LoopBreakLemma(u, v, i, alpha, beta, old_value, value, minimax_v);
            break;
          }
          LoopMaintenanceLemma(u, v, i, alpha, beta, old_value, value, minimax_v);
        }

        return value;
      }
      else // if u.color == White
      {
        var value: bounded_int := alpha;

        for i := 0 to |u.children|
          invariant 0 <= i <= |u.children|
          invariant alpha <= value
          invariant is_partial_minimax_ab_result(value, u, i, alpha, beta)
          invariant i == |u.children| ==> is_minimax_ab_result(value, u, alpha, beta)
        {
          ghost var old_value := value;

          var v := u.children[i];
          var minimax_v := Minimax(v, alpha, beta);

          value := max(value, minimax_v);
          if value >= beta
          {
            LoopBreakLemma(u, v, i, alpha, beta, old_value, value, minimax_v);
            break;
          }
          LoopMaintenanceLemma(u, v, i, alpha, beta, old_value, value, minimax_v);
        }

        return value;
      }
    }
  }

  // Proves correctness when alpha-beta pruning triggers early loop termination
  lemma LoopBreakLemma(u: Node, v: Node, i: nat, alpha: bounded_int, beta: bounded_int, old_value: bounded_int, value: bounded_int, minimax_v: bounded_int)
    requires 0 <= i < |u.children|
    requires v == u.children[i]
    requires u.color == Black ==> value == min(old_value, minimax_v)
    requires u.color == White ==> value == max(old_value, minimax_v)
    requires u.color == Black ==> value <= alpha
    requires u.color == White ==> value >= beta
    requires is_partial_minimax_ab_result(old_value, u, i, alpha, beta)
    requires is_minimax_ab_result(minimax_v, v, alpha, beta)
    ensures is_minimax_ab_result(value, u, alpha, beta)
  {
    ChildrenAppendLemma(u, i);
  }

  // Proves loop invariant maintenance for minimax alpha-beta algorithm
  lemma LoopMaintenanceLemma(u: Node, v: Node, i: nat, alpha: bounded_int, beta: bounded_int, old_value: bounded_int, value: bounded_int, minimax_v: bounded_int)
    requires 0 <= i < |u.children|
    requires v == u.children[i]
    requires u.color == Black ==> value == min(old_value, minimax_v)
    requires u.color == White ==> value == max(old_value, minimax_v)
    requires u.color == Black ==> value > alpha
    requires u.color == White ==> value < beta
    requires is_partial_minimax_ab_result(old_value, u, i, alpha, beta)
    requires is_minimax_ab_result(minimax_v, v, alpha, beta)
    ensures is_partial_minimax_ab_result(value, u, i + 1, alpha, beta)
    ensures i == |u.children| - 1 ==> is_minimax_ab_result(value, u, alpha, beta)
  {
    ChildrenAppendLemma(u, i);
    if i == |u.children| - 1
    {
      assert |u.children| > 0;
    }
  }

} // MinimaxKnuth1975Module

// Based on Fishburn 1983 (fail-soft)
abstract module MinimaxABFishburn1983Module
{
  import opened Definitions
  import opened Lemmas

  class MinimaxFishburn1983Algorithm
  {
    // Minimax with fail-soft alpha-beta pruning: returns exact values outside window
    method Minimax(u: Node, alpha: bounded_int, beta: bounded_int) returns (result: bounded_int)
      requires alpha < beta
      ensures is_minimax_ab_result(result, u, alpha, beta)
    {
      if |u.children| == 0
      {
        return u.eval;
      }
      else if u.color == Black
      {
        var value: bounded_int := INFINITY;

        for i := 0 to |u.children|
          invariant 0 <= i <= |u.children|
          invariant alpha < value
          invariant is_partial_minimax_ab_result(value, u, i, alpha, beta)
        {
          ghost var old_value := value;

          var v := u.children[i];
          var minimax_v := Minimax(v, alpha, min(value, beta));
          value := min(value, minimax_v);

          if value <= alpha
          {
            LoopBreakLemma(u, v, i, alpha, beta, old_value, value, minimax_v);
            break;
          }
          LoopMaintenanceLemma(u, v, i, alpha, beta, old_value, value, minimax_v);
        }

        return value;
      }
      else // if u.color == White
      {
        var value: bounded_int := alpha;

        for i := 0 to |u.children|
          invariant 0 <= i <= |u.children|
          invariant value < beta
          invariant is_partial_minimax_ab_result(value, u, i, alpha, beta)
        {
          ghost var old_value := value;

          var v := u.children[i];
          var minimax_v := Minimax(v, max(value, alpha), beta);
          value := max(value, minimax_v);

          if value >= beta
          {
            LoopBreakLemma(u, v, i, alpha, beta, old_value, value, minimax_v);
            break;
          }
          LoopMaintenanceLemma(u, v, i, alpha, beta, old_value, value, minimax_v);
        }

        return value;
      }
    }
  }

  // Proves correctness when fail-soft alpha-beta pruning triggers early termination
  lemma LoopBreakLemma(u: Node, v: Node, i: nat, alpha: bounded_int, beta: bounded_int, old_value: bounded_int, value: bounded_int, minimax_v: bounded_int)
    requires alpha < beta
    requires 0 <= i < |u.children|
    requires v == u.children[i]
    requires u.color == Black ==> value <= alpha
    requires u.color == Black ==> value == min(old_value, minimax_v)
    requires u.color == Black ==> is_minimax_ab_result(minimax_v, v, alpha, min(old_value, beta))
    requires u.color == White ==> value >= beta
    requires u.color == White ==> value == max(old_value, minimax_v)
    requires u.color == White ==> is_minimax_ab_result(minimax_v, v, max(old_value, alpha), beta)
    requires is_partial_minimax_ab_result(old_value, u, i, alpha, beta)
    ensures is_minimax_ab_result(value, u, alpha, beta)
  {
    ChildrenAppendLemma(u, i);
    PartialMinimaxLemma(u);
  }

  // Proves loop invariant maintenance for fail-soft minimax alpha-beta algorithm
  lemma LoopMaintenanceLemma(u: Node, v: Node, i: nat, alpha: bounded_int, beta: bounded_int, old_value: bounded_int, value: bounded_int, minimax_v: bounded_int)
    requires 0 <= i < |u.children|
    requires v == u.children[i]
    requires u.color == Black ==> value > alpha
    requires u.color == Black ==> value == min(old_value, minimax_v)
    requires u.color == Black ==> is_minimax_ab_result(minimax_v, v, alpha, min(old_value, beta))
    requires u.color == White ==> value < beta
    requires u.color == White ==> value == max(old_value, minimax_v)
    requires u.color == White ==> is_minimax_ab_result(minimax_v, v, max(old_value, alpha), beta)
    requires is_partial_minimax_ab_result(old_value, u, i, alpha, beta)
    ensures is_partial_minimax_ab_result(value, u, i + 1, alpha, beta)
    ensures i == |u.children| - 1 ==> is_minimax_ab_result(value, u, alpha, beta)
  {
    ChildrenAppendLemma(u, i);
    if i == |u.children| - 1
    {
      assert |u.children| > 0;
    }
  }

} // MinimaxFishburn1983Module

// Based on Wikipedia 2025
abstract module MinimaxABWiki2025Module
{
  import opened Definitions
  import opened Lemmas

  class MinimaxABWiki2025Algorithm
  {
    // Minimax with enhanced fail-soft alpha-beta pruning: dynamically adjusts window bounds
    method Minimax(u: Node, alpha0: bounded_int, beta0: bounded_int) returns (result: bounded_int)
      requires alpha0 < beta0
      ensures is_minimax_ab_result(result, u, alpha0, beta0)
    {
      var alpha := alpha0;
      var beta := beta0;

      if |u.children| == 0
      {
        return u.eval;
      }
      else if u.color == Black
      {
        var value: bounded_int := INFINITY;

        for i := 0 to |u.children|
          invariant 0 <= i <= |u.children|
          invariant alpha0 == alpha < beta <= beta0
          invariant value >= beta0 ==> beta == beta0
          invariant alpha0 < value < beta0 ==> value == beta
          invariant is_partial_minimax_ab_result(value, u, i, alpha0, beta0)
        {
          ghost var old_value := value;
          ghost var old_beta := beta;

          var v := u.children[i];
          var minimax_v := Minimax(v, alpha, beta);
          value := min(value, minimax_v);
          beta := min(beta, value);

          if alpha >= beta
          {
            LoopBreakLemma(u, v, i, alpha, beta, alpha0, beta0, 0, old_beta, value, old_value, minimax_v);
            break;
          }
          LoopMaintenanceLemma(u, v, i, alpha, beta, alpha0, beta0, 0, old_beta, value, old_value, minimax_v);
        }

        return value;
      }
      else // if u.color == White
      {
        ghost var old_alpha := alpha;

        var value: bounded_int := alpha;

        for i := 0 to |u.children|
          invariant 0 <= i <= |u.children|
          invariant alpha0 <= alpha < beta == beta0
          invariant value <= alpha0 ==> alpha == alpha0
          invariant alpha0 < value < beta0 ==> value == alpha
          invariant is_partial_minimax_ab_result(value, u, i, alpha0, beta0)
        {
          ghost var old_value := value;
          ghost var old_alpha := alpha;

          var v := u.children[i];
          var minimax_v := Minimax(v, alpha, beta);
          value := max(value, minimax_v);
          alpha := max(alpha, value);

          if alpha >= beta
          {
            LoopBreakLemma(u, v, i, alpha, beta, alpha0, beta0, old_alpha, 0, value, old_value, minimax_v);
            break;
          }
          LoopMaintenanceLemma(u, v, i, alpha, beta, alpha0, beta0, old_alpha, 0, value, old_value, minimax_v);
        }

        return value;
      }
    }
  }

  // Proves correctness when enhanced alpha-beta pruning with dynamic bounds triggers termination
  lemma LoopBreakLemma(u: Node, v: Node, i: nat, alpha: bounded_int, beta: bounded_int, alpha0: bounded_int, beta0: bounded_int, old_alpha: bounded_int, old_beta: bounded_int, value: bounded_int, old_value: bounded_int, minimax_v: bounded_int)
    requires 0 <= i < |u.children|
    requires v == u.children[i]
    requires u.color == Black ==> alpha0 == alpha < old_beta <= beta0
    requires u.color == Black ==> is_minimax_ab_result(minimax_v, v, alpha, old_beta)
    requires u.color == Black ==> value == min(old_value, minimax_v)
    requires u.color == Black ==> beta == min(old_beta, value)
    requires u.color == Black ==> alpha >= beta
    requires u.color == White ==> alpha0 <= old_alpha < beta == beta0
    requires u.color == White ==> is_minimax_ab_result(minimax_v, v, old_alpha, beta)
    requires u.color == White ==> value == max(old_value, minimax_v)
    requires u.color == White ==> alpha == max(old_alpha, value)
    requires u.color == White ==> alpha >= beta
    requires is_partial_minimax_ab_result(old_value, u, i, alpha0, beta0)
    ensures is_minimax_ab_result(value, u, alpha0, beta0)
  {
    ChildrenAppendLemma(u, i);
    PartialMinimaxLemma(u);
  }

  // Proves loop invariant maintenance for enhanced minimax alpha-beta with dynamic bounds
  lemma LoopMaintenanceLemma(u: Node, v: Node, i: nat, alpha: bounded_int, beta: bounded_int, alpha0: bounded_int, beta0: bounded_int, old_alpha: bounded_int, old_beta: bounded_int, value: bounded_int, old_value: bounded_int, minimax_v: bounded_int)
    requires 0 <= i < |u.children|
    requires v == u.children[i]
    requires u.color == Black ==> alpha0 == alpha < old_beta <= beta0
    requires u.color == Black ==> is_minimax_ab_result(minimax_v, v, alpha, old_beta)
    requires u.color == Black ==> value == min(old_value, minimax_v)
    requires u.color == Black ==> alpha0 < old_value < beta0 ==> old_value == old_beta
    requires u.color == Black ==> old_value >= beta0 ==> old_beta == beta0
    requires u.color == White ==> alpha0 <= old_alpha < beta == beta0
    requires u.color == White ==> is_minimax_ab_result(minimax_v, v, old_alpha, beta)
    requires u.color == White ==> value == max(old_value, minimax_v)
    requires u.color == White ==> old_value <= alpha0 ==> old_alpha == alpha0
    requires u.color == White ==> alpha0 < old_value < beta0 ==> old_value == old_alpha
    requires is_partial_minimax_ab_result(old_value, u, i, alpha0, beta0)
    ensures is_partial_minimax_ab_result(value, u, i + 1, alpha0, beta0)
    ensures i == |u.children| - 1 ==> is_minimax_ab_result(value, u, alpha0, beta0)
  {
    ChildrenAppendLemma(u, i);
    if i == |u.children| - 1
    {
      assert |u.children| > 0;
      PartialMinimaxLemma(u);
    }
  }

} // MinimaxABWiki2025Module
