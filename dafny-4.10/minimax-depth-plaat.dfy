// Copyright: Wieger Wesselink 2026
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)

include "definitions.dfy"
include "lemmas.dfy"

// Implementation of the depth-limited MT-SSS* / minimax-Plaat algorithm from the paper
// "Best-first Fixed-depth Minimax algorithms" by Plaat et al. (1996).

abstract module MinimaxDepthPlaat1996Module
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

  ghost predicate is_minimax_tt_result(value: bounded_int, u: Node, alpha: bounded_int, beta: bounded_int, depth: nat)
  {
    exists u': Node :: is_expansion(u', u, depth) && is_minimax_ab_result(value, u', alpha, beta)
  }

  datatype PlaatTableEntry = PlaatTableEntry_(lowerbound: bounded_int, upperbound: bounded_int, depth: nat)
  type PlaatTranspositionTable = map<Node, PlaatTableEntry>

  ghost predicate is_valid_table_entry(t: PlaatTableEntry, u: Node)
  {
    (t.upperbound < INFINITY ==> exists u': Node :: is_expansion(u', u, t.depth) && t.upperbound >= minimax(u')) &&
    (t.lowerbound > -INFINITY ==> exists u': Node :: is_expansion(u', u, t.depth) && t.lowerbound <= minimax(u'))
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
    ensures t.lowerbound >= beta ==> is_minimax_tt_result(t.lowerbound, u, alpha, beta, depth)
    ensures t.upperbound <= alpha ==> is_minimax_tt_result(t.upperbound, u, alpha, beta, depth)
  {
    reveal is_minimax_ab_result();
    if t.lowerbound >= beta
    {
      assert t.lowerbound > -INFINITY;
      var u': Node :| is_expansion(u', u, t.depth) && t.lowerbound <= minimax(u');
      ExpansionDecreaseDepthLemma(u', u, t.depth);
      assert is_expansion(u', u, depth);
    }
    if t.upperbound <= alpha
    {
      assert t.upperbound < INFINITY;
      var u': Node :| is_expansion(u', u, t.depth) && t.upperbound >= minimax(u');
      ExpansionDecreaseDepthLemma(u', u, t.depth);
      assert is_expansion(u', u, depth);
    }
  }

  lemma TableUpdateLemma(result: bounded_int, u: Node, alpha0: bounded_int, beta0: bounded_int, depth: nat, T: PlaatTranspositionTable)
    requires alpha0 < beta0
    requires is_valid_table(T)
    requires is_minimax_tt_result(result, u, alpha0, beta0, depth)
    ensures
      var lower := if result > alpha0 then result else -INFINITY;
      var upper := if result < beta0 then result else INFINITY;
      is_valid_table(T[u := PlaatTableEntry_(lower, upper, depth)])
  {
    reveal is_minimax_ab_result();
  }

  class MinimaxDepthPlaat1996Algorithm
  {
    var T: PlaatTranspositionTable

    // Implementation of the depth-limited MT-SSS* / minimax version of Plaat et al. 1996.
    method Minimax(u: Node, alpha0: bounded_int, beta0: bounded_int, depth: nat) returns (result: bounded_int)
      requires turn_based()
      requires alpha0 < beta0
      requires is_valid_table(T)
      modifies this`T
      ensures is_minimax_tt_result(result, u, alpha0, beta0, depth)
      ensures is_valid_table(T)
      decreases depth, u
    {
      reveal partial_minimax();
      reveal is_minimax_ab_result();

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
          invariant i > 0 ==> exists u': Node :: is_expansion(u', u, depth) && is_partial_minimax_ab_result(value, u', i, alpha0, beta0)
          invariant i == |u.children| ==> is_minimax_tt_result(value, u, alpha0, beta0, depth)
        {
          ghost var old_beta := beta;
          ghost var old_value := value;

          var v := u.children[i];
          var minimax_v := Minimax(v, alpha0, beta, depth - 1);
          value := min(value, minimax_v);
          beta := min(beta, value);

          if beta <= alpha0
          {
            LoopBreakBlackLemma(u, v, i, depth, alpha0, beta0, old_beta, old_value, beta, value, minimax_v);
            break;
          }
          LoopMaintenanceBlackLemma(u, v, i, depth, alpha0, beta0, old_beta, old_value, beta, value, minimax_v);
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
          invariant i > 0 ==> exists u': Node :: is_expansion(u', u, depth) && is_partial_minimax_ab_result(value, u', i, alpha0, beta0)
          invariant i == |u.children| ==> is_minimax_tt_result(value, u, alpha0, beta0, depth)
        {
          ghost var old_alpha := alpha;
          ghost var old_value := value;

          var v := u.children[i];
          var minimax_v := Minimax(v, alpha, beta0, depth - 1);
          value := max(value, minimax_v);
          alpha := max(alpha, value);

          if alpha >= beta0
          {
            LoopBreakWhiteLemma(u, v, i, depth, alpha0, beta0, old_alpha, old_value, alpha, value, minimax_v);
            break;
          }
          LoopMaintenanceWhiteLemma(u, v, i, depth, alpha0, beta0, old_alpha, old_value, alpha, value, minimax_v);
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
    ensures is_minimax_tt_result(u.eval, u, alpha0, beta0, depth)
  {
    reveal is_minimax_ab_result();
    ghost var u' := truncate_at_depth(u, 0);
    ghost var value := u.eval;
    assert is_expansion(u', u, depth);
    assert is_minimax_ab_result(value, u', alpha0, beta0);
  }

  lemma LoopBreakWhiteHelperLemma(u: Node, u': Node, v: Node, v': Node, i: nat, depth: nat, alpha0: bounded_int, beta0: bounded_int, old_bound: bounded_int, old_value: bounded_int, bound: bounded_int, value: bounded_int, minimax_v: bounded_int)
    requires 0 <= i < |u.children|
    requires |u.children| == |u'.children|
    requires u' == replace_child(u, i, v')
    requires u.color == Black ==> (value == min(old_value, minimax_v) && bound == min(old_bound, value) && value <= alpha0 && alpha0 < old_bound <= beta0)
    requires u.color == White ==> (value == max(old_value, minimax_v) && bound == max(old_bound, value) && value >= beta0 && alpha0 <= old_bound < beta0)
    requires is_minimax_ab_result(minimax_v, v', (if u.color == Black then alpha0 else old_bound), (if u.color == Black then old_bound else beta0))
    requires is_partial_minimax_ab_result(old_value, u, i, alpha0, beta0)
    ensures is_minimax_ab_result(value, u', alpha0, beta0)
  {
    reveal partial_minimax();
    reveal is_minimax_ab_result();
    reveal is_ab_result();

    MinimaxMinMaxLemma(u', i);
    PartialMinimaxLemma(u');
    ChildrenAppendLemma(u, i);
    if u.color == Black {
      assert alpha0 < old_bound;
    } else {
      assert old_bound < beta0;
    }
    IsABResultLemma(minimax_v, minimax(v'), (if u.color == Black then alpha0 else old_bound), (if u.color == Black then old_bound else beta0));
    IsABResultLemma(old_value, partial_minimax(u, i), alpha0, beta0);
    IsABResultLemma(value, minimax(u'), alpha0, beta0);
  }

  lemma LoopBreakBlackLemma(u: Node, v: Node, i: nat, depth: nat, alpha0: bounded_int, beta0: bounded_int, old_beta: bounded_int, old_value: bounded_int, beta: bounded_int, value: bounded_int, minimax_v: bounded_int)
    requires turn_based()
    requires u.color == Black
    requires 0 <= i < |u.children|
    requires depth > 0
    requires v == u.children[i]
    requires beta <= alpha0
    requires alpha0 < old_beta <= beta0
    requires value == min(old_value, minimax_v)
    requires beta == min(old_beta, value)
    requires is_minimax_tt_result(minimax_v, v, alpha0, old_beta, depth - 1)
    requires i == 0 ==> old_value == INFINITY && old_beta == beta0
    requires i > 0 ==> exists u': Node :: is_expansion(u', u, depth) && is_partial_minimax_ab_result(old_value, u', i, alpha0, beta0)
    ensures is_minimax_tt_result(value, u, alpha0, beta0, depth)
  {
    reveal partial_minimax();
    reveal is_minimax_ab_result();
    var v': Node :| is_expansion(v', v, depth - 1) && is_minimax_ab_result(minimax_v, v', alpha0, old_beta);

    if i > 0 
    {
      var u': Node :| is_expansion(u', u, depth) && is_partial_minimax_ab_result(old_value, u', i, alpha0, beta0);
      var u'' := replace_child(u', i, v');
      LoopBreakWhiteHelperLemma(u', u'', v, v', i, depth, alpha0, beta0, old_beta, old_value, beta, value, minimax_v);
      assert is_expansion(u'', u, depth);
    }
    else
    {
      var u' := replace_child(u, i, v');
      ExpansionReplaceChildLemma(u, u', v, v', i, depth);
      LoopBreakWhiteHelperLemma(u, u', v, v', i, depth, alpha0, beta0, old_beta, old_value, beta, value, minimax_v);
    }
  }

  lemma LoopBreakWhiteLemma(u: Node, v: Node, i: nat, depth: nat, alpha0: bounded_int, beta0: bounded_int, old_alpha: bounded_int, old_value: bounded_int, alpha: bounded_int, value: bounded_int, minimax_v: bounded_int)
    requires turn_based()
    requires u.color == White
    requires 0 <= i < |u.children|
    requires depth > 0
    requires v == u.children[i]
    requires alpha >= beta0
    requires alpha0 <= old_alpha < beta0
    requires value == max(old_value, minimax_v)
    requires alpha == max(old_alpha, value)
    requires is_minimax_tt_result(minimax_v, v, old_alpha, beta0, depth - 1)
    requires i == 0 ==> old_value == -INFINITY && old_alpha == alpha0
    requires i > 0 ==> exists u': Node :: is_expansion(u', u, depth) && is_partial_minimax_ab_result(old_value, u', i, alpha0, beta0)
    ensures is_minimax_tt_result(value, u, alpha0, beta0, depth)
  {
    reveal partial_minimax();
    reveal is_minimax_ab_result();
    var v': Node :| is_expansion(v', v, depth - 1) && is_minimax_ab_result(minimax_v, v', old_alpha, beta0);

    if i > 0 
    {
      var u': Node :| is_expansion(u', u, depth) && is_partial_minimax_ab_result(old_value, u', i, alpha0, beta0);
      var u'' := replace_child(u', i, v');
      LoopBreakWhiteHelperLemma(u', u'', v, v', i, depth, alpha0, beta0, old_alpha, old_value, alpha, value, minimax_v);
      assert is_expansion(u'', u, depth);
    }
    else
    {
      var u' := replace_child(u, i, v');
      ExpansionReplaceChildLemma(u, u', v, v', i, depth);
      LoopBreakWhiteHelperLemma(u, u', v, v', i, depth, alpha0, beta0, old_alpha, old_value, alpha, value, minimax_v);
    }
  }

  lemma LoopMaintenanceWhiteLemma(u: Node, v: Node, i: nat, depth: nat, alpha0: bounded_int, beta0: bounded_int, old_alpha: bounded_int, old_value: bounded_int, alpha: bounded_int, value: bounded_int, minimax_v: bounded_int)
    requires turn_based()
    requires u.color == White
    requires 0 <= i < |u.children|
    requires depth > 0
    requires v == u.children[i]
    requires alpha0 <= old_alpha < beta0
    requires old_value <= alpha0 ==> old_alpha == alpha0
    requires alpha < beta0
    requires alpha0 < old_value < beta0 ==> old_alpha == old_value
    requires value == max(old_value, minimax_v)
    requires alpha == max(old_alpha, value)
    requires is_minimax_tt_result(minimax_v, v, old_alpha, beta0, depth - 1)
    requires i == 0 ==> old_value == -INFINITY && old_alpha == alpha0
    requires i > 0 ==> exists u': Node :: is_expansion(u', u, depth) && is_partial_minimax_ab_result(old_value, u', i, alpha0, beta0)
    ensures exists u': Node :: is_expansion(u', u, depth) && is_partial_minimax_ab_result(value, u', i + 1, alpha0, beta0)
    ensures i == |u.children| - 1 ==> is_minimax_tt_result(value, u, alpha0, beta0, depth)
  {
    reveal partial_minimax();
    reveal is_minimax_ab_result();

    var v': Node :| is_expansion(v', v, depth - 1) && is_minimax_ab_result(minimax_v, v', old_alpha, beta0);

    if i > 0
    {
      var u': Node :| is_expansion(u', u, depth) && is_partial_minimax_ab_result(old_value, u', i, alpha0, beta0);
      var u'' := replace_child(u', i, v');
      assert is_expansion(u'', u, depth);
      LoopMaintenanceWhiteHelperLemma(u', u'', v, v', i, depth, alpha0, beta0, old_alpha, old_value, alpha, value, minimax_v);
      if i == |u.children| - 1
      {
        PartialMinimaxAlphaBetaLemma(value, u'', i + 1, alpha0, beta0);
      }
    }
    else
    {
      var u'' := replace_child(u, i, v');
      ExpansionReplaceChildLemma(u, u'', v, v', i, depth);
      LoopMaintenanceWhiteHelperLemma(u, u'', v, v', i, depth, alpha0, beta0, old_alpha, old_value, alpha, value, minimax_v);
      if i == |u.children| - 1
      {
        PartialMinimaxAlphaBetaLemma(value, u'', i + 1, alpha0, beta0);
      }
    }
  }

  lemma LoopMaintenanceBlackLemma(u: Node, v: Node, i: nat, depth: nat, alpha0: bounded_int, beta0: bounded_int, old_beta: bounded_int, old_value: bounded_int, beta: bounded_int, value: bounded_int, minimax_v: bounded_int)
    requires turn_based()
    requires u.color == Black
    requires 0 <= i < |u.children|
    requires depth > 0
    requires v == u.children[i]
    requires alpha0 < old_beta <= beta0
    requires old_value >= beta0 ==> old_beta == beta0
    requires beta > alpha0
    requires alpha0 < old_value < beta0 ==> old_beta == old_value
    requires value == min(old_value, minimax_v)
    requires beta == min(old_beta, value)
    requires is_minimax_tt_result(minimax_v, v, alpha0, old_beta, depth - 1)
    requires i == 0 ==> old_value == INFINITY && old_beta == beta0
    requires i > 0 ==> exists u': Node :: is_expansion(u', u, depth) && is_partial_minimax_ab_result(old_value, u', i, alpha0, beta0)
    ensures exists u': Node :: is_expansion(u', u, depth) && is_partial_minimax_ab_result(value, u', i + 1, alpha0, beta0)
    ensures i == |u.children| - 1 ==> is_minimax_tt_result(value, u, alpha0, beta0, depth)
  {
    reveal partial_minimax();
    reveal is_minimax_ab_result();
    var v': Node :| is_expansion(v', v, depth - 1) && is_minimax_ab_result(minimax_v, v', alpha0, old_beta);
                                                      
    if i > 0 
    {
      var u': Node :| is_expansion(u', u, depth) && is_partial_minimax_ab_result(old_value, u', i, alpha0, beta0);
      var u'' := replace_child(u', i, v');
      assert is_expansion(u'', u, depth);
      LoopMaintenanceBlackHelperLemma(u', u'', v, v', i, depth, alpha0, beta0, old_beta, old_value, beta, value, minimax_v);
      if i == |u.children| - 1
      {
        PartialMinimaxAlphaBetaLemma(value, u'', i + 1, alpha0, beta0);
      }
    }
    else
    {
      var u'' := replace_child(u, i, v');
      ExpansionReplaceChildLemma(u, u'', v, v', i, depth);
      LoopMaintenanceBlackHelperLemma(u, u'', v, v', i, depth, alpha0, beta0, old_beta, old_value, beta, value, minimax_v);
      if i == |u.children| - 1
      {
        PartialMinimaxAlphaBetaLemma(value, u'', i + 1, alpha0, beta0);
      }
    }
  }

  lemma LoopMaintenanceWhiteHelperLemma(u': Node, u'': Node, v: Node, v': Node, i: nat, depth: nat, alpha0: bounded_int, beta0: bounded_int, old_alpha: bounded_int, old_value: bounded_int, alpha: bounded_int, value: bounded_int, minimax_v: bounded_int)
    requires u'.color == White
    requires 0 <= i < |u'.children|
    requires |u'.children| == |u''.children|
    requires u'' == replace_child(u', i, v')
    requires alpha < beta0

    requires old_value <= alpha0 ==> old_alpha == alpha0
    requires alpha0 <= old_alpha < beta0
    requires alpha0 < old_value < beta0 ==> old_alpha == old_value

    requires value == max(old_value, minimax_v)
    requires alpha == max(old_alpha, value)
    requires is_minimax_ab_result(minimax_v, v', old_alpha, beta0)
    requires is_partial_minimax_ab_result(old_value, u', i, alpha0, beta0)
    ensures  is_partial_minimax_ab_result(value, u'', i + 1, alpha0, beta0)
  {
    reveal is_minimax_ab_result();
    reveal partial_minimax();
    MinimaxMinMaxLemma(u'', i);
  }

  lemma LoopMaintenanceBlackHelperLemma(u': Node, u'': Node, v: Node, v': Node, i: nat, depth: nat, alpha0: bounded_int, beta0: bounded_int, old_beta: bounded_int, old_value: bounded_int, beta: bounded_int, value: bounded_int, minimax_v: bounded_int)
    requires u'.color == Black
    requires 0 <= i < |u'.children|
    requires |u'.children| == |u''.children|
    requires u'' == replace_child(u', i, v')
    requires beta > alpha0
    requires alpha0 < old_beta <= beta0
    requires old_value >= beta0 ==> old_beta == beta0
    requires alpha0 < old_value < beta0 ==> old_beta == old_value
    requires value == min(old_value, minimax_v)
    requires beta == min(old_beta, value)
    requires is_minimax_ab_result(minimax_v, v', alpha0, old_beta)    
    requires is_partial_minimax_ab_result(old_value, u', i, alpha0, beta0)
    ensures  is_partial_minimax_ab_result(value, u'', i + 1, alpha0, beta0)
  {
    reveal is_minimax_ab_result();
    reveal partial_minimax();
    MinimaxMinMaxLemma(u'', i);
  }

} // module MinimaxDepthPlaat1996Module
