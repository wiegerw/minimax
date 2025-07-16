// Copyright: Wieger Wesselink 2023
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)

include "definitions.dfy"

// Test module with concrete definitions for algorithm verification
module Definitions' refines Definitions
{
  const UNSPECIFIED_POSITIVE_NUMBER := 100
}

abstract module TestModule
{
  import opened Definitions'

  // Test depth truncation with simple tree structure
  method TestTruncateDepth1()
  {
    //     a
    //    / \
    //   b   c

    var b := Node_(3, Color.Black, []);
    var c := Node_(7, Color.Black, []);
    var a := Node_(2, Color.White, [b, c]);

    var T := a;
    
    assert truncate_at_depth(b, 0) == b;
    assert truncate_at_depth(c, 0) == c;
    assert truncate_at_depth(a, 0) == Node_(2, Color.White, []);
    assert truncate_at_depth_list([c], 0) == [c];
    assert truncate_at_depth_list([b, c], 0) == [b, c];
    assert truncate_at_depth(T, 1) == T;
  }

  // Test depth truncation with more complex tree structure
  method TestTruncateDepth2()
  {
    //         a
    //       /   \
    //      b     c
    //     / \     \
    //    d   e    f

    var d := Node_(7, Color.White, []);
    var e := Node_(2, Color.Black, []);
    var f := Node_(6, Color.White, []);
    var b := Node_(4, Color.Black, [d, e]);
    var c := Node_(3, Color.Black, [f]);
    var a := Node_(5, Color.White, [b, c]);

    var b0 := Node_(4, Color.Black, []);
    var c0 := Node_(3, Color.Black, []);
    var a1 := Node_(5, Color.White, [b0, c0]);
    assert truncate_at_depth(b, 0) == b0;
    assert truncate_at_depth(c, 0) == c0;
    assert truncate_at_depth_list([c], 0) == [c0];
    assert truncate_at_depth_list([b, c], 0) == [b0, c0];
    assert truncate_at_depth(a, 1) == a1;
  }
} // TestModule
