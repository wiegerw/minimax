// Copyright: Wieger Wesselink 2023
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)

include "definitions.dfy"
include "lemmas.dfy"

// Negamax with alpha-beta pruning for efficient game tree search
// https://en.wikipedia.org/wiki/Negamax

// The F2 function of Knuth 1975 (fail-hard)
abstract module NegamaxABKnuth1975Module
{
  import opened Definitions
  import opened Lemmas

  class NegamaxKnuth1975Algorithm
  {
    // Negamax with alpha-beta pruning: combines negamax simplicity with pruning efficiency
    method Negamax(u: Node, alpha: bounded_int, beta: bounded_int) returns (result: bounded_int)
      requires turn_based()
      requires alpha < beta
      ensures is_negamax_ab_result(result, u, alpha, beta)
    {
      reveal partial_negamax();
      reveal is_negamax_ab_result();

      if |u.children| == 0
      {
        return color(u) * u.eval;
      }
      else
      {
        var value: bounded_int := alpha;

        for i := 0 to |u.children|
          invariant turn_based()
          invariant 0 <= i <= |u.children|
          invariant alpha <= value < beta
          invariant is_partial_negamax_ab_result(value, u, i, alpha, beta)
          invariant i == |u.children| ==> is_negamax_ab_result(value, u, alpha, beta)
        {
          ghost var old_value := value;

          var v := u.children[i];
          var Negamax_v := Negamax(v, -beta, -value);

          value := max(value, -Negamax_v);
          if value >= beta
          {
            LoopBreakLemma(u, v, i, alpha, beta, old_value, value, Negamax_v);
            break;
          }

          LoopMaintenanceLemma(u, v, i, alpha, beta, old_value, value, Negamax_v);
        }

        return value;
      }
    }
  }

  // Proves correctness when negamax alpha-beta pruning triggers early loop termination
  lemma LoopBreakLemma(u: Node, v: Node, i: nat, alpha: bounded_int, beta: bounded_int, old_value: bounded_int, value: bounded_int, negamax_v: bounded_int)
    requires turn_based()
    requires 0 <= i < |u.children|
    requires v == u.children[i]
    requires value == max(old_value, -negamax_v)
    requires value >= beta
    requires is_partial_negamax_ab_result(old_value, u, i, alpha, beta)
    requires is_negamax_ab_result(negamax_v, v, -beta, -old_value)
    ensures is_negamax_ab_result(value, u, alpha, beta)
  {
    reveal partial_negamax();
    reveal is_negamax_ab_result();
    ChildrenAppendLemma(u, i);
    PartialNegamaxLemma(u);
  }

  // Proves loop invariant maintenance for negamax alpha-beta algorithm
  lemma LoopMaintenanceLemma(u: Node, v: Node, i: nat, alpha: bounded_int, beta: bounded_int, old_value: bounded_int, value: bounded_int, negamax_v: bounded_int)
    requires turn_based()
    requires 0 <= i < |u.children|
    requires v == u.children[i]
    requires value == max(old_value, -negamax_v)
    requires value < beta
    requires is_partial_negamax_ab_result(old_value, u, i, alpha, beta)
    requires is_negamax_ab_result(negamax_v, v, -beta, -old_value)
    ensures is_partial_negamax_ab_result(value, u, i + 1, alpha, beta)
    ensures i == |u.children| - 1 ==> is_negamax_ab_result(value, u, alpha, beta)
  {
    reveal partial_negamax();
    reveal is_negamax_ab_result();
    ChildrenAppendLemma(u, i);
    if i == |u.children| - 1
    {
      assert |u.children| > 0;
      PartialNegamaxLemma(u);
    }
  }
} // NegamaxKnuth1975Module

// The fab function of Fishburn 1983 (fail-soft)
abstract module NegamaxABFishburn1983Module
{
  import opened Definitions
  import opened Lemmas

  class NegamaxFishburn1983Algorithm
  {
    method Negamax(u: Node, alpha: bounded_int, beta: bounded_int) returns (result: bounded_int)
      requires turn_based()
      requires alpha < beta
      ensures is_negamax_ab_result(result, u, alpha, beta)
    {
      reveal partial_negamax();
      reveal is_negamax_ab_result();

      if |u.children| == 0
      {
        return color(u) * u.eval;
      }
      else
      {
        var value: bounded_int := -INFINITY;
        for i := 0 to |u.children|
          invariant 0 <= i <= |u.children|
          invariant value < beta
          invariant is_partial_negamax_ab_result(value, u, i, alpha, beta)
          invariant i == |u.children| ==> is_negamax_ab_result(value, u, alpha, beta)
        {
          ghost var old_value := value;
          var v := u.children[i];
          var negamax_v := Negamax(v, -beta, -max(value, alpha));
          value := max(value, -negamax_v);
          if value >= beta
          {
            LoopBreakLemma(u, v, i, alpha, beta, old_value, value, negamax_v);
            break;
          }
          LoopMaintenanceLemma(u, v, i, alpha, beta, old_value, value, negamax_v);
        }
        return value;
      }
    }
  }

  lemma LoopBreakLemma(u: Node, v: Node, i: nat, alpha: bounded_int, beta: bounded_int, old_value: bounded_int, value: bounded_int, negamax_v: bounded_int)
    requires turn_based()
    requires 0 <= i < |u.children|
    requires v == u.children[i]
    requires value == max(old_value, -negamax_v)
    requires value >= beta
    requires is_partial_negamax_ab_result(old_value, u, i, alpha, beta)
    requires is_negamax_ab_result(negamax_v, v, -beta, -max(old_value, alpha))
    ensures is_negamax_ab_result(value, u, alpha, beta)
  {
    reveal partial_negamax();
    reveal is_negamax_ab_result();
    ChildrenAppendLemma(u, i);
    PartialNegamaxLemma(u);
  }

  lemma LoopMaintenanceLemma(u: Node, v: Node, i: nat, alpha: bounded_int, beta: bounded_int, old_value: bounded_int, value: bounded_int, negamax_v: bounded_int)
    requires turn_based()
    requires 0 <= i < |u.children|
    requires v == u.children[i]
    requires value == max(old_value, -negamax_v)
    requires value < beta
    requires is_partial_negamax_ab_result(old_value, u, i, alpha, beta)
    requires is_negamax_ab_result(negamax_v, v, -beta, -max(old_value, alpha))
    ensures is_partial_negamax_ab_result(value, u, i + 1, alpha, beta)
    ensures i == |u.children| - 1 ==> is_negamax_ab_result(value, u, alpha, beta)
  {
    reveal partial_negamax();
    reveal is_negamax_ab_result();
    ChildrenAppendLemma(u, i);
    if i == |u.children| - 1
    {
      assert |u.children| > 0;
      PartialNegamaxLemma(u);
    }
  }
} // module NegamaxFishburn1983Module

// The Wikipedia version (enhanced fail-soft)
abstract module NegamaxWikipedia2025Module
{
  import opened Definitions
  import opened Lemmas

  class NegamaxABWikipedia2025Algorithm
  {
    method Negamax(u: Node, alpha0: bounded_int, beta0: bounded_int) returns (result: bounded_int)
      requires alpha0 < beta0
      requires turn_based()
      ensures is_negamax_ab_result(result, u, alpha0, beta0)
    {
      reveal partial_negamax();
      reveal is_negamax_ab_result();
      var alpha := alpha0;
      if |u.children| == 0
      {
        return color(u) * u.eval;
      }
      else
      {
        var value: bounded_int := -INFINITY;
        for i := 0 to |u.children|
          invariant 0 <= i <= |u.children|
          invariant alpha0 <= alpha < beta0
          invariant value <= alpha0 ==> alpha == alpha0
          invariant alpha0 < value < beta0 ==> value == alpha
          invariant is_partial_negamax_ab_result(value, u, i, alpha0, beta0)
          invariant i == |u.children| ==> is_negamax_ab_result(value, u, alpha0, beta0)
        {
          ghost var old_alpha := alpha;
          ghost var old_value := value;
          var v := u.children[i];
          var negamax_v := Negamax(v, -beta0, -alpha);
          value := max(value, -negamax_v);
          alpha := max(alpha, value);
          if alpha >= beta0
          {
            LoopBreakLemma(u, v, i, alpha0, beta0, old_alpha, alpha, old_value, value, negamax_v);
            break;
          }
          LoopMaintenanceLemma(u, v, i, alpha0, beta0, old_alpha, alpha, old_value, value, negamax_v);
        }
        return value;
      }
    }
  }

  lemma LoopBreakLemma(u: Node, v: Node, i: nat, alpha0: bounded_int, beta0: bounded_int, old_alpha: bounded_int, alpha: bounded_int, old_value: bounded_int, value: bounded_int, negamax_v: bounded_int)
    requires turn_based()
    requires 0 <= i < |u.children|
    requires v == u.children[i]
    requires alpha >= beta0
    requires old_alpha < beta0
    requires value == max(old_value, -negamax_v)
    requires alpha == max(old_alpha, value)
    requires is_partial_negamax_ab_result(old_value, u, i, alpha0, beta0)
    requires is_negamax_ab_result(negamax_v, v, -beta0, -old_alpha)
    requires old_value > beta0 ==> partial_negamax(u, i) >= old_value
    ensures is_negamax_ab_result(value, u, alpha0, beta0)
  {
    reveal partial_negamax();
    reveal is_negamax_ab_result();
    ChildrenAppendLemma(u, i);
    PartialNegamaxLemma(u);
  }

  lemma LoopMaintenanceLemma(u: Node, v: Node, i: nat, alpha0: bounded_int, beta0: bounded_int, old_alpha: bounded_int, alpha: bounded_int, old_value: bounded_int, value: bounded_int, negamax_v: bounded_int)
    requires turn_based()
    requires 0 <= i < |u.children|
    requires v == u.children[i]
    requires old_value <= alpha0 ==> old_alpha == alpha0
    requires alpha0 < old_value < beta0 ==> old_value == old_alpha
    requires value == max(old_value, -negamax_v)
    requires alpha == max(old_alpha, value)
    requires alpha < beta0
    requires is_partial_negamax_ab_result(old_value, u, i, alpha0, beta0)
    requires is_negamax_ab_result(negamax_v, v, -beta0, -old_alpha)
    ensures is_partial_negamax_ab_result(value, u, i + 1, alpha0, beta0)
    ensures i == |u.children| - 1 ==> is_negamax_ab_result(value, u, alpha0, beta0)
  {
    reveal partial_negamax();
    reveal is_negamax_ab_result();
    ChildrenAppendLemma(u, i);
    if i == |u.children| - 1
    {
      assert |u.children| > 0;
      PartialNegamaxLemma(u);
    }
  }
} // module NegamaxWikipedia2025Module

// A small variation of the Wikipedia version (alpha > beta instead of alpha >= beta).
abstract module NegamaxWikipedia2025'Module
{
  import opened Definitions
  import opened Lemmas

  class NegamaxWikipedia2025'Algorithm
  {
    method Negamax(u: Node, alpha0: bounded_int, beta0: bounded_int) returns (result: bounded_int)
      requires turn_based()
      requires alpha0 <= beta0
      ensures is_negamax_ab_result(result, u, alpha0, beta0)
    {
      var alpha := alpha0;

      if |u.children| == 0
      {
        NoChildrenReturnLemma(u, alpha0, beta0);
        return color(u) * u.eval;
      }
      else
      {
        var value: bounded_int := -INFINITY;

        LoopEntryLemma(u, alpha0, beta0, alpha, value);
        for i := 0 to |u.children|
          invariant 0 <= i <= |u.children|
          invariant alpha0 <= alpha <= beta0
          invariant value <= alpha0 ==> alpha == alpha0
          invariant alpha0 < value < beta0 ==> value == alpha
          invariant is_partial_negamax_ab_result(value, u, i, alpha0, beta0)
          invariant i == |u.children| ==> is_negamax_ab_result(value, u, alpha0, beta0)
        {
          ghost var old_alpha := alpha;
          ghost var old_value := value;

          var v := u.children[i];

          var negamax_v := Negamax(v, -beta0, -alpha);

          value := max(value, -negamax_v);
          alpha := max(alpha, value);
          if alpha > beta0  // NegamaxWikipedia2025 uses >=
          {
            LoopBreakLemma(u, v, i, alpha0, beta0, old_alpha, alpha, old_value, value, negamax_v);
            break;
          }
          LoopMaintenanceLemma(u, v, i, alpha0, beta0, old_alpha, alpha, old_value, value, negamax_v);
        }
        return value;
      }
    }
  }

  lemma NoChildrenReturnLemma(u: Node, alpha0: bounded_int, beta0: bounded_int)
    requires |u.children| == 0 
    ensures is_negamax_ab_result(color(u) * u.eval, u, alpha0, beta0)
  {
    reveal is_negamax_ab_result();
  }

  lemma LoopEntryLemma(u: Node, alpha0: bounded_int, beta0: bounded_int, alpha: bounded_int, value: bounded_int)
    requires value == -INFINITY
    requires alpha == alpha0 <= beta0
    requires |u.children| > 0
    ensures is_partial_negamax_ab_result(value, u, 0, alpha0, beta0)
  {
    reveal partial_negamax();
  }

  lemma LoopBreakLemma(u: Node, v: Node, i: nat, alpha0: bounded_int, beta0: bounded_int, old_alpha: bounded_int, alpha: bounded_int, old_value: bounded_int, value: bounded_int, negamax_v: bounded_int)
    requires turn_based()
    requires 0 <= i < |u.children|
    requires v == u.children[i]
    requires alpha > beta0
    requires alpha0 <= old_alpha <= beta0
    requires value == max(old_value, -negamax_v)
    requires alpha == max(old_alpha, value)
    requires is_negamax_ab_result(negamax_v, v, -beta0, -old_alpha)
    requires old_value > beta0 ==> partial_negamax(u, i) >= old_value 
    ensures is_negamax_ab_result(value, u, alpha0, beta0)
  {
    reveal partial_negamax();
    reveal is_negamax_ab_result();
    ChildrenAppendLemma(u, i);
    PartialNegamaxLemma(u);
  }

  lemma LoopMaintenanceLemma(u: Node, v: Node, i: nat, alpha0: bounded_int, beta0: bounded_int, old_alpha: bounded_int, alpha: bounded_int, old_value: bounded_int, value: bounded_int, negamax_v: bounded_int)
    requires turn_based()
    requires 0 <= i < |u.children|
    requires v == u.children[i]
    requires alpha <= beta0
    requires old_value <= alpha0 ==> old_alpha == alpha0
    requires alpha0 < old_value < beta0 ==> old_value == old_alpha
    requires value == max(old_value, -negamax_v)
    requires alpha == max(old_alpha, value)
    requires is_negamax_ab_result(negamax_v, v, -beta0, -old_alpha)
    requires is_partial_negamax_ab_result(old_value, u, i, alpha0, beta0)
    ensures alpha0 <= alpha <= beta0
    ensures value <= alpha0 ==> alpha == alpha0
    ensures alpha0 < value < beta0 ==> value == alpha
    ensures is_partial_negamax_ab_result(value, u, i + 1, alpha0, beta0)
    ensures i == |u.children| - 1 ==> is_negamax_ab_result(value, u, alpha0, beta0)
  {
    reveal partial_negamax();
    reveal is_negamax_ab_result();
    ChildrenAppendLemma(u, i);

    if i == |u.children| - 1
    {
      assert |u.children| > 0;
      PartialNegamaxLemma(u);
    }
  }

} // module NegamaxWikipedia2025'Module
