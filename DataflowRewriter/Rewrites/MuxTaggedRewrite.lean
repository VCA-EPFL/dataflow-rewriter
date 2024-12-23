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

    i_t -> mux [to = "inp0"];
    i_f -> mux [to = "inp1"];
    i_c -> mux [to = "inp2"];

    i_tag -> join [to = "inp0"];

    mux -> join [from = "out0", to = "inp1"];

    join -> o_out [from = "out0"];
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
    branch [type = "branch"];

    i_c -> fork [to = "inp0"];

    fork -> branch [from = "out0", to = "cond"];
    i_tag -> branch [to = "val"];

    branch -> join_t [from = "true", to = "inp0"];
    i_t -> join_t [to = "inp1"];

    branch -> join_f [from = "false", to = "inp0"];
    i_f -> join_f [to = "inp1"];

    join_t -> mux [from = "out0", to = "inp0"];
    join_f -> mux [from = "out0", to = "inp1"];
    fork -> mux [from = "out1", to = "inp2"];

    mux -> o_out [from = "out0"];
  ]

def rhsLower := rhs.lower.get rfl

def rewrite : Rewrite String :=
  { abstractions := [],
    pattern := matcher,
    input_expr := lhsLower,
    output_expr := rhsLower }

end DataflowRewriter.MuxTaggedRewrite
