/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.Rewriter
import DataflowRewriter.ExprHighElaborator

namespace DataflowRewriter.MergeRewrite

def matcher (g : ExprHigh String) : RewriteResult (List String) := do
  let (.some list) ← g.modules.foldlM (λ nodes inst (pmap, typ) => do
      if nodes.isSome then return nodes
      unless typ = "merge" do return none
      let nn ←
        try followOutput g inst "out0"
        catch
          | .error s => return none
          | .done => throw .done
      unless nn.typ = "merge" do return none
      unless nn.inputPort = "inp0" do return none
      return some [inst, nn.inst]
    ) none | throw .done
  return list

@[drunfold] def mergeIn : ExprHigh String := [graph|
    out0 [mod = "io"];
    inp0 [mod = "io"];
    inp1 [mod = "io"];
    inp2 [mod = "io"];

    merge1 [mod = "merge"];
    merge2 [mod = "merge"];

    inp0 -> merge1 [inp = "inp0"];
    inp1 -> merge1 [inp = "inp1"];
    inp2 -> merge2 [inp = "inp1"];

    merge1 -> merge2 [out = "out0", inp = "inp0"];

    merge2 -> out0 [out = "out0"];
  ]

def mergeInLower := mergeIn.lower.get rfl

@[drunfold] def mergeOut : ExprHigh String := [graph|
    out0 [mod = "io"];
    inp0 [mod = "io"];
    inp1 [mod = "io"];
    inp2 [mod = "io"];

    merge3 [mod = "merge3"];

    inp0 -> merge3 [inp = "inp0"];
    inp1 -> merge3 [inp = "inp1"];
    inp2 -> merge3 [inp = "inp2"];

    merge3 -> out0 [out = "out0"];
  ]

def mergeOutLower := mergeOut.lower.get rfl

def rewrite : Rewrite String :=
  { pattern := matcher,
    input_expr := mergeInLower,
    output_expr := mergeOutLower }

namespace TestRewriter

def mergeHigh : ExprHigh String :=
  [graph|
    src0 [mod="io"];
    snk0 [mod="io"];

    fork1 [mod="fork"];
    fork2 [mod="fork"];
    merge2 [mod="merge"];
    merge1 [mod="merge"];

    src0 -> fork1 [inp="out0"];

    fork1 -> fork2 [out="out0",inp="inp0"];

    fork1 -> merge1 [out="out1",inp="inp0"];
    fork2 -> merge1 [out="out0",inp="inp1"];
    fork2 -> merge2 [out="out1",inp="inp1"];

    merge1 -> merge2 [out="out0",inp="inp0"];

    merge2 -> snk0 [out="out0"];
  ]

#eval DataflowRewriter.rewrite "rw0_" mergeHigh rewrite |> toString |> IO.print

end TestRewriter

end DataflowRewriter.MergeRewrite
