/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.Rewriter
import DataflowRewriter.ExprHighElaborator

namespace DataflowRewriter.ForkRewrite

/--
The matcher takes in a dot graph and should return the cluster of nodes that
form the subgraph as a list of instance names.
-/
def matcher (g : ExprHigh String) : RewriteResult (List String) := do
  let (.some list) ← g.modules.foldlM (λ nodes inst (pmap, typ) => do
      if nodes.isSome then return nodes
      unless typ = "Fork" do return none
      let (.some nn) := followOutput g inst "out1" | return none
      unless nn.typ = "Fork" && nn.inputPort = "inp0" do return none
      return some [inst, nn.inst]
    ) none | throw .done
  return list

@[drunfold] def Lhs : ExprHigh String := [graph|
    out0 [type = "io"];
    out1 [type = "io"];
    out2 [type = "io"];
    inp0 [type = "io"];

    fork1 [type = "Fork"];
    fork2 [type = "Fork"];

    inp0 -> fork1 [inp = "inp0"];

    fork1 -> out0 [out = "out0"];
    fork1 -> fork2 [out = "out1", inp = "inp0"];

    fork2 -> out1 [out = "out0"];
    fork2 -> out2 [out = "out1"];
  ]

/--
To get instances in a predictable order, it's a good idea to extract the whole
graph once with the nodes in the order that you want to provide them in the
pattern-matcher.  In this case we want fork1 to be listed before fork2.
-/
def LhsOrdered := Lhs.extract ["fork1", "fork2"] |>.get rfl

/--
Graph extraction gives back two graphs, the subgraph and the rest of the graph.
Here we just double check that the rest of the graph is empty, implying we
extracted the whole graph.  The proof of `rfl` should always work for this.
-/
theorem double_check_empty_snd : LhsOrdered.snd = ExprHigh.mk ∅ ∅ := by rfl

/--
We then use the extracted graph to lower to ExprLow, which ensures the right
ordering of instances.
-/
def LhsLower := LhsOrdered.fst.lower.get rfl

@[drunfold] def Rhs : ExprHigh String := [graph|
    out0 [type = "io"];
    out1 [type = "io"];
    out2 [type = "io"];
    inp0 [type = "io"];

    fork3 [type = "Fork3"];

    inp0 -> fork3 [inp = "inp0"];

    fork3 -> out0 [out = "out0"];
    fork3 -> out1 [out = "out1"];
    fork3 -> out2 [out = "out2"];
  ]

def RhsLower := Rhs.lower.get rfl

def rewrite : Rewrite String :=
  { pattern := matcher,
    input_expr := LhsLower,
    output_expr := RhsLower }

namespace TestRewriter

def fullCircuit : ExprHigh String :=
  [graph|
    src0 [type="io"];
    snk0 [type="io"];

    fork1 [type="Fork"];
    fork2 [type="Fork"];
    merge2 [type="merge"];
    merge1 [type="merge"];

    src0 -> fork1 [inp="inp0"];

    fork1 -> fork2 [out="out1",inp="inp0"];

    fork1 -> merge1 [out="out0",inp="inp0"];
    fork2 -> merge1 [out="out0",inp="inp1"];
    fork2 -> merge2 [out="out1",inp="inp1"];

    merge1 -> merge2 [out="out0",inp="inp0"];

    merge2 -> snk0 [out="out0"];
  ]

#eval DataflowRewriter.rewrite "rw0_" fullCircuit rewrite |> toString |> IO.print

end TestRewriter

end DataflowRewriter.ForkRewrite
