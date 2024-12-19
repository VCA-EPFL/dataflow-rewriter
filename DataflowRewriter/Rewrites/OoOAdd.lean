/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.Rewriter
import DataflowRewriter.ExprHighElaborator

namespace DataflowRewriter.OoOAdd

def matcher (g : ExprHigh String) : RewriteResult (List String) := sorry

def lhs : ExprHigh String := [graph|
    i_0 [type = "io"];
    i_1 [type = "io"];
    i_2 [type = "io"];
    o_out [type = "io"];

    join [type = "FixedSize.join"];
    joinL [type = "FixedSize.joinP"];

    i_1 -> join [inp = "inp0"];
    i_2 -> join [inp = "inp1"];

    i_0 -> joinL [inp = "inp0"];

    join -> joinL [out = "out0", inp = "inp1"];

    joinL -> o_out [out = "out0"];
  ]

def lhs_extract := lhs.extract ["join", "joinL"] |>.get rfl

theorem double_check_empty_snd : lhs_extract.snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := lhs_extract.fst.lower.get rfl

def rhs : ExprHigh String := [graph|
    i_0 [type = "io"];
    i_1 [type = "io"];
    i_2 [type = "io"];
    o_out [type = "io"];

    join_0 [type = "FixedSize.join"];
    join_1 [type = "FixedSize.joinL"];

    i_0 -> join_0 [inp = "inp0"];
    i_1 -> join_0 [inp = "inp1"];

    i_2 -> join_1 [inp = "inp1"];

    join_0 -> join_1 [out = "out0", inp = "inp0"];

    join_1 -> o_out [out = "out0"];
  ]

def rhsLower := rhs.lower.get rfl

def rewrite : Rewrite String :=
  { abstractions := [],
    pattern := matcher,
    input_expr := lhsLower,
    output_expr := rhsLower }

end DataflowRewriter.OoOAdd
