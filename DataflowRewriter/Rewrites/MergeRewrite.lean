/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.Rewriter
import DataflowRewriter.ExprHighElaborator

namespace DataflowRewriter.MergeRewrite

/--
The matcher takes in a dot graph and should return the cluster of nodes that
form the subgraph as a list of instance names.
-/
def matcher (g : ExprHigh String) : RewriteResult (List String) := do
  let (.some list) ← g.modules.foldlM (λ nodes inst (pmap, typ) => do
      if nodes.isSome then return nodes
      unless typ = "merge" do return none
      let (.some nn) := followOutput g inst "out0" | return none
      unless nn.typ = "merge" && nn.inputPort = "inp0" do return none
      return some [inst, nn.inst]
    ) none | throw .done
  return list

@[drunfold] def mergeLhs : ExprHigh String := [graph|
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

#eval IO.print mergeLhs

/--
To get instances in a predictable order, it's a good idea to extract the whole
graph once with the nodes in the order that you want to provide them in the
pattern-matcher.  In this case we want merge1 to be listed before merge2.
-/
def mergeLhsOrdered := mergeLhs.extract ["merge1", "merge2"] |>.get rfl

/--
Graph extraction gives back two graphs, the subgraph and the rest of the graph.
Here we just double check that the rest of the graph is empty, implying we
extracted the whole graph.  The proof of `rfl` should always work for this.
-/
theorem double_check_empty_snd : mergeLhsOrdered.snd = ExprHigh.mk ∅ ∅ := by rfl

/--
We then use the extracted graph to lower to ExprLow, which ensures the right
ordering of instances.
-/
def mergeLhsLower := mergeLhsOrdered.fst.lower.get rfl

@[drunfold] def mergeRhs : ExprHigh String := [graph|
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

#eval IO.print mergeRhs

def mergeRhsLower := mergeRhs.lower.get rfl

def rewrite : Rewrite String :=
  { pattern := matcher,
    input_expr := mergeLhsLower,
    output_expr := mergeRhsLower }

namespace TestRewriter

def mergeHigh : ExprHigh String :=
  [graph|
    src0 [mod="io"];
    snk0 [mod="io"];

    fork1 [mod="fork"];
    fork2 [mod="fork"];
    merge2 [mod="merge"];
    merge1 [mod="merge"];

    src0 -> fork1 [inp="inp0"];

    fork1 -> fork2 [out="out0",inp="inp0"];

    fork1 -> merge1 [out="out1",inp="inp0"];
    fork2 -> merge1 [out="out0",inp="inp1"];
    fork2 -> merge2 [out="out1",inp="inp1"];

    merge1 -> merge2 [out="out0",inp="inp0"];

    merge2 -> snk0 [out="out0"];
  ]

/--
info: ok: digraph {

  snk0 [mod = "io", label = "snk0: io"];
  src0 [mod = "io", label = "src0: io"];
  rw0_2 [mod = "merge3", label = "rw0_2: merge3"];
  rw0_1 [mod = "fork", label = "rw0_1: fork"];
  rw0_0 [mod = "fork", label = "rw0_0: fork"];


  rw0_2 -> snk0 [out = "out0", taillabel = "out0"];
  src0 -> rw0_0 [inp = "inp0", headlabel = "inp0"];

  rw0_0 -> rw0_1 [out = "out0", inp = "inp0", taillabel = "out0", headlabel = "inp0",];
  rw0_0 -> rw0_2 [out = "out1", inp = "inp0", taillabel = "out1", headlabel = "inp0",];
  rw0_1 -> rw0_2 [out = "out0", inp = "inp1", taillabel = "out0", headlabel = "inp1",];
  rw0_1 -> rw0_2 [out = "out1", inp = "inp1", taillabel = "out1", headlabel = "inp1",];
}
-/
#guard_msgs in
#eval DataflowRewriter.rewrite "rw0_" mergeHigh rewrite |> toString |> IO.print

end TestRewriter

end DataflowRewriter.MergeRewrite
