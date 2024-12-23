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
      unless typ = "Merge" do return none
      let (.some nn) := followOutput g inst "out0" | return none
      unless nn.typ = "Merge" && nn.inputPort = "inp0" do return none
      return some [inst, nn.inst]
    ) none | throw .done
  return list

@[drunfold] def mergeLhs : ExprHigh String := [graph|
    out0 [type = "io"];
    inp0 [type = "io"];
    inp1 [type = "io"];
    inp2 [type = "io"];

    merge1 [type = "Merge"];
    merge2 [type = "Merge"];

    inp0 -> merge1 [to = "inp0"];
    inp1 -> merge1 [to = "inp1"];
    inp2 -> merge2 [to = "inp1"];

    merge1 -> merge2 [from = "out0", to = "inp0"];

    merge2 -> out0 [from = "out0"];
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
    out0 [type = "io"];
    inp0 [type = "io"];
    inp1 [type = "io"];
    inp2 [type = "io"];

    merge3 [type = "Merge3"];

    inp0 -> merge3 [to = "inp0"];
    inp1 -> merge3 [to = "inp1"];
    inp2 -> merge3 [to = "inp2"];

    merge3 -> out0 [from = "out0"];
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
    src0 [type="io"];
    snk0 [type="io"];

    fork1 [type="Fork"];
    fork2 [type="Fork"];
    merge2 [type="Merge"];
    merge1 [type="Merge"];

    src0 -> fork1 [to="inp0"];

    fork1 -> fork2 [from="out0",to="inp0"];

    fork1 -> merge1 [from="out1",to="inp0"];
    fork2 -> merge1 [from="out0",to="inp1"];
    fork2 -> merge2 [from="out1",to="inp1"];

    merge1 -> merge2 [from="out0",to="inp0"];

    merge2 -> snk0 [from="out0"];
  ]

/-
info: ok: digraph {

  snk0 [mod = "io", label = "snk0: io"];
  src0 [mod = "io", label = "src0: io"];
  rw0_2 [mod = "merge3", label = "rw0_2: merge3"];
  rw0_1 [mod = "fork", label = "rw0_1: fork"];
  rw0_0 [mod = "fork", label = "rw0_0: fork"];


  rw0_2 -> snk0 [from = "out0", taillabel = "out0"];
  src0 -> rw0_0 [to = "inp0", headlabel = "inp0"];

  rw0_0 -> rw0_1 [from = "out0", to = "inp0", taillabel = "out0", headlabel = "inp0",];
  rw0_0 -> rw0_2 [from = "out1", to = "inp0", taillabel = "out1", headlabel = "inp0",];
  rw0_1 -> rw0_2 [from = "out0", to = "inp1", taillabel = "out0", headlabel = "inp1",];
  rw0_1 -> rw0_2 [from = "out1", to = "inp1", taillabel = "out1", headlabel = "inp1",];
}
-/
-- #guard_msgs in
-- #eval DataflowRewriter.rewrite "rw0_" mergeHigh rewrite |> toString |> IO.print

end TestRewriter

end DataflowRewriter.MergeRewrite
