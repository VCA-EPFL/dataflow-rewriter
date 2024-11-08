/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martina Camaioni
-/

import DataflowRewriter.Rewriter
import DataflowRewriter.ExprHighElaborator

namespace DataflowRewriter.MuxTaggedRewrite

def matcher (g : ExprHigh String) : RewriteResult (List String) := sorry

def lhs' : ExprHigh String := [graph|
    i_t [type = "io"];
    i_f [type = "io"];
    i_c [type = "io"];
    i_tag [type = "io"];
    o_out [type = "io"];

    mux [type = "mux"];
    join [type = "join"];

    i_t -> mux [inp = "inp0"];
    i_f -> mux [inp = "inp1"];
    i_c -> mux [inp = "inp2"];

    i_tag -> join [inp = "inp0"];

    mux -> join [out = "out0", inp = "inp1"];

    join -> o_out [out = "out0"];
  ]

def lhs := lhs'.extract ["mux", "join"] |>.get rfl

theorem double_check_empty_snd : lhs.snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := lhs.fst.lower.get rfl

def rhs : ExprHigh String := [graph|
    i_t [type = "io"];
    i_f [type = "io"];
    i_c [type = "io"];
    i_tag [type = "io"];
    o_out [type = "io"];

    mux [type = "tagged_mux"];
    join_t [type = "join"];
    join_f [type = "join"];
    fork [type = "fork"];

    i_tag -> fork [inp = "inp0"];

    fork -> join_t [out = "out0", inp = "inp0"];
    i_t -> join_t [inp = "inp1"];

    fork -> join_f [out = "out1", inp = "inp0"];
    i_f -> join_f [inp = "inp1"];

    join_t -> mux [out = "out0", inp = "inp0"];
    join_f -> mux [out = "out0", inp = "inp1"];
    i_c -> mux [inp = "inp2"];

    mux -> o_out [out = "out0"];
  ]

def rhsLower := rhs.lower.get rfl

def rewrite : Rewrite String :=
  { abstractions := [],
    pattern := matcher,
    input_expr := lhsLower,
    output_expr := rhsLower }

end DataflowRewriter.MuxTaggedRewrite
