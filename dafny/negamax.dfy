// Copyright: Wieger Wesselink 2023
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)

include "definitions.dfy"
include "lemmas.dfy"

// Basic negamax algorithm: simplified minimax using sign flipping
// https://en.wikipedia.org/wiki/Negamax

// Classic negamax

abstract module NegamaxModule
{
  import opened Definitions
  import opened Lemmas

  class NegamaxAlgorithm
  {
    // Standard negamax: equivalent to minimax but with unified perspective
    method Negamax(u: Node) returns (result: bounded_int)
      requires turn_based()
      ensures result == negamax(u)
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
          invariant value == partial_negamax(u, i)
          invariant i == |u.children| ==> value == negamax(u)
        {
          ghost var old_value := value;
          var v := u.children[i];
          var negamax_v := Negamax(v);
          value := max(value, -negamax_v);
          LoopMaintenanceLemma(u, v, i, value, old_value, negamax_v);
        }
        return value;
      }
    }
  }

  // Proves loop invariant maintenance for negamax algorithm
  lemma LoopMaintenanceLemma(u: Node, v: Node, i: nat, value: int, old_value: bounded_int, negamax_v: bounded_int)
    requires turn_based()
    requires 0 <= i < |u.children|
    requires v == u.children[i]
    requires old_value == partial_negamax(u, i)
    requires negamax_v == negamax(v)
    requires value == max(old_value, -negamax_v)
    ensures value == partial_negamax(u, i + 1)
    ensures i == |u.children| - 1 ==> value == negamax(u)
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
 
} // module NegamaxModule
