/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat
-/

import DataflowRewriter.Rewriter
import DataflowRewriter.ExprHighElaborator

namespace DataflowRewriter.BranchInorderMux2Merge

-- TODO: 2 inputs, 2 outputs for the taggrCntrlAligner:
-- enq_untagged, complete_tagged are the input ports
-- tagged, deq_untagged are the output ones

/--
Matcher used for abstraction of the left module. Currently we do not check that the Mux and Branch are paired
so it could probably be unsafe (what would happen?).
-/
def matchModLeft (g : ExprHigh String) : RewriteResult (List String) := do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
      if s.isSome then return s
      unless typ = "TaggerCntrlAligner" do return none
      let (.some branch_nn) := followInput g inst "enq_untagged" | return none
      unless branch_nn.typ = "Branch" && branch_nn.inputPort = "true" do return none
      let (.some begin_m) := followOutput g inst "tagged" | return none
      let (.some end_m) := followInput g inst "complete_tagged" | return none
      let (.some mux_nn) := followOutput g inst "deq_untagged" | return none
      unless mux_nn.typ = "Merge" do return none
      let (.some scc) := findSCCNodes g begin_m.inst end_m.inst | return none
      return some scc
    ) none | throw .done
  return list


/--
Matcher used for abstraction of the right module
-/
def matchModRight (g : ExprHigh String) : RewriteResult (List String) := do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
      if s.isSome then return s
      unless typ = "TaggerCntrlAligner" do return none
      let (.some branch_nn) := followInput g inst "enq_untagged" | return none
      unless branch_nn.typ = "Branch" && branch_nn.inputPort = "false" do return none
      let (.some begin_m) := followOutput g inst "tagged" | return none
      let (.some end_m) := followInput g inst "complete_tagged" | return none
      let (.some mux_nn) := followOutput g inst "deq_untagged" | return none
      unless mux_nn.typ = "Merge" do return none
      let (.some scc) := findSCCNodes g begin_m.inst end_m.inst | return none
      return some scc
    ) none | throw .done
  return list


def matcher (g : ExprHigh String) : RewriteResult (List String) := do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
      if s.isSome then return s
      unless typ = "Branch" do return none

      let (.some taggerL) := followOutput g inst "true" | return none
      let (.some taggerR) := followOutput g inst "false" | return none

      -- We do not double check we got the right type, as the name of the port should be enough?
      let (.some begin_l) := followOutput g taggerL.inst "tagged" | return none
      let (.some end_l) := followInput g taggerL.inst "complete_tagged" | return none
      let (.some begin_r) := followOutput g taggerR.inst "tagged" | return none
      let (.some end_r) := followInput g taggerR.inst "complete_tagged" | return none
      unless (begin_l.typ = "mod_left") && (begin_r.typ = "mod_right") && (begin_l.inst = end_l.inst) && (begin_r.inst = end_r.inst) do return none
      let (.some mux_nn) := followOutput g taggerL.inst "deq_untagged" | return none
      unless mux_nn.typ = "Merge" do return none
      -- We do not double check that the Mux match the Branch.

      return some [inst, taggerL.inst, taggerR.inst, begin_l.inst, begin_r.inst, mux_nn.inst]
    ) none | throw .done
  return list

def lhs' : ExprHigh String := [graph|
    i_data [type = "io"];
    i_cond [type = "io"];
    o_out [type = "io"];

    branch [type = "Branch"];
    tagger1 [type = "TaggerCntrlAligner"];
    tagger2 [type = "TaggerCntrlAligner"];
    m_left [type = "mod_left"];
    m_right [type = "mod_right"];
    merge [type = "Merge"];

    i_cond -> branch [inp = "cond"];

    branch -> tagger1 [out = "true", inp = "enq_untagged"];
    branch -> tagger2 [out = "false", inp = "enq_untagged"];

    tagger1 -> m_left [out = "tagged", inp="m_in"];
    tagger2 -> m_right [out = "tagged", inp="m_in"];

    m_left -> tagger1 [out = "m_out", inp = "complete_tagged"];
    m_right -> tagger2 [out = "m_out", inp = "complete_tagged"];

    tagger1 -> merge [out = "deq_untagged", inp = "inp0"];
    tagger2 -> merge [out = "deq_untagged", inp = "inp1"];

    merge -> o_out [out = "out0"];
  ]

def lhs := lhs'.extract ["branch", "tagger1", "tagger2", "m_left", "m_right", "merge"] |>.get rfl

theorem double_check_empty_snd : lhs.snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := lhs.fst.lower.get rfl


def rhs : ExprHigh String := [graph|
    i_data [type = "io"];
    i_cond [type = "io"];
    o_out [type = "io"];

    branch [type = "Branch"];
    join [type = "Join"];
    split [type = "Split"];
    tagger [type = "TaggerCntrlAligner"];
    m_left [type = "mod_left"];
    m_right [type = "mod_right"];
    merge [type = "Merge"];


    i_data -> join [inp = "inp0"];
    i_cond -> join [inp = "inp1"];

    join -> tagger [out = "out0", inp = "enq_untagged"];
    tagger -> split [inp ="inp0", out = "tagged"];

    split -> branch [out = "out0", inp = "data"];
    split -> branch [out = "out1", inp = "cond"];

    branch -> m_left [out = "true", inp="m_in"];
    branch -> m_right [out = "false", inp="m_in"];


    m_left-> merge [out = "m_out", inp = "inp0"];
    m_right -> merge [out = "m_out", inp = "inp1"];
    merge -> tagger [out = "m_out", inp = "complete_tagged"];

    tagger -> o_out [out = "deq_untagged"];
  ]

def rhsLower := rhs.lower.get rfl
-- Double checking that the left and right abstracter seems to work:
#eval matchModRight lhs'
#eval matchModLeft lhs'
#eval matcher lhs'
#eval IO.print lhs'


/--
This rewrite adds abstractions to the definition, which provide patterns to
extract parts of the graph.  The `type` given to each extracted node has to
match the `type` of the node in LHS and RHS graphs.
-/
def rewrite : Rewrite String :=
  { abstractions := [⟨matchModLeft, "mod_left"⟩, ⟨matchModRight, "mod_right"⟩],
    pattern := matcher,
    input_expr := lhsLower,
    output_expr := rhsLower }

namespace TEST

def lhs' : ExprHigh String :=
[graph|
    i_data [type = "io"];
    i_cond [type = "io"];
    o_out [type = "io"];

    branch [type = "Branch"];
    tagger1 [type = "TaggerCntrlAligner"];
    tagger2 [type = "TaggerCntrlAligner"];
    m_left1 [type = "mod_left1"];
    m_left2 [type = "mod_left2"];
    m_right [type = "mod_right2"];
    merge [type = "Merge"];

    i_cond -> branch [inp = "cond"];

    merge -> o_out [out = "out0"];

    branch -> tagger1 [out = "true", inp = "enq_untagged"];
    branch -> tagger2 [out = "false", inp = "enq_untagged"];

    tagger1 -> m_left1 [out = "tagged", inp="m_in"];
    tagger2 -> m_right [out = "tagged", inp="m_in"];

    m_left1 -> m_left2 [out="m_out", inp="m_in"];

    m_left2 -> tagger1 [out = "m_out", inp = "complete_tagged"];
    m_right -> tagger2 [out = "m_out", inp = "complete_tagged"];

    tagger1 -> merge [out = "deq_untagged", inp = "inp0"];
    tagger2 -> merge [out = "deq_untagged", inp = "inp1"];

  ]

#eval _root_.DataflowRewriter.rewrite "rw0_" lhs' rewrite |>.toOption |>.get! |> IO.print

end TEST

end DataflowRewriter.BranchInorderMux2Merge
