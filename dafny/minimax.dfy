// Copyright: Wieger Wesselink 2023
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)

include "definitions.dfy"
include "lemmas.dfy"

// Basic minimax algorithm without alpha-beta pruning
// https://en.wikipedia.org/wiki/Alpha%E2%80%93beta_pruning

abstract module MinimaxModule
{
  import opened Definitions
  import opened Lemmas

  class Minimax
  {
    // Standard minimax algorithm: explores entire game tree
    method Minimax(u: Node) returns (result: bounded_int)
      ensures result == minimax(u)
    {
      if |u.children| == 0
      {
        return u.eval;
      }
      else if u.color == Color.Black
      {
        var value := INFINITY;
        for i := 0 to |u.children|
          invariant 0 <= i <= |u.children|
          invariant value == partial_minimax(u, i)
          invariant i == |u.children| ==> value == minimax(u)
        {
          ghost var old_value := value;
          var v := u.children[i];
          var minimax_v := Minimax(v);
          value := min(value, minimax_v);
          LoopMaintenanceLemma(u, v, i, value, old_value, minimax_v);
        }
        return value;
      }
      else
      {
        var value := -INFINITY;
        for i := 0 to |u.children|
          invariant 0 <= i <= |u.children|
          invariant value == partial_minimax(u, i)
          invariant i == |u.children| ==> value == minimax(u)
        {
          ghost var old_value := value;
          var v := u.children[i];
          var minimax_v := Minimax(v);
          value := max(value, minimax_v);
          LoopMaintenanceLemma(u, v, i, value, old_value, minimax_v);
        }
        return value;
      }
    }
  }

  // Proves loop invariant maintenance for minimax algorithm
  lemma LoopMaintenanceLemma(u: Node, v: Node, i: nat, value: int, old_value: bounded_int, minimax_v: bounded_int)
    requires 0 <= i < |u.children|
    requires v == u.children[i]
    requires old_value == partial_minimax(u, i)
    requires minimax_v == minimax(v)
    requires u.color == Black ==> value == min(old_value, minimax_v)
    requires u.color == White ==> value == max(old_value, minimax_v)
    ensures value == partial_minimax(u, i + 1)
    ensures i == |u.children| - 1 ==> value == minimax(u)
  {
    ChildrenAppendLemma(u, i);
    if i == |u.children| - 1
    {
      assert |u.children| > 0;
      PartialMinimaxLemma(u);
    }
  }
}
