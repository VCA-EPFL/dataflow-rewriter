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
    i_t [mod = "io"];
    i_f [mod = "io"];
    i_c [mod = "io"];
    i_tag [mod = "io"];
    o_out [mod = "io"];

    mux [mod = "mux"];
    join [mod = "join"];

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
    i_t [mod = "io"];
    i_f [mod = "io"];
    i_c [mod = "io"];
    i_tag [mod = "io"];
    o_out [mod = "io"];

    mux [mod = "tagged_mux"];
    join_t [mod = "join"];
    join_f [mod = "join"];
    fork [mod = "fork"];
    branch [mod = "branch"];



    i_c -> fork [inp = "inp0"];

    fork -> branch [out = "out0", inp = "cond"];
    i_tag -> branch [inp = "val"];

    branch -> join_t [out = "true", inp = "inp0"];
    i_t -> join_t [inp = "inp1"];

    branch -> join_f [out = "false", inp = "inp0"];
    i_f -> join_f [inp = "inp1"];

    join_t -> mux [out = "out0", inp = "inp0"];
    join_f -> mux [out = "out0", inp = "inp1"];
    fork -> mux [out = "out1", inp = "inp2"];

    mux -> o_out [out = "out0"];
  ]

def rhsLower := rhs.lower.get rfl

def rewrite : Rewrite String :=
  { abstractions := [],
    pattern := matcher,
    input_expr := lhsLower,
    output_expr := rhsLower }

end DataflowRewriter.MuxTaggedRewrite
