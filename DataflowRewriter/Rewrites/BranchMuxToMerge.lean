/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.Rewriter
import DataflowRewriter.ExprHighElaborator

namespace DataflowRewriter.BranchMuxToMerge

-- The following namespace just shows two alternative definitions of the matcher
-- and the abstraction matcher that use the domination algorithm instead of
-- following the condition signal.  This is unfortunately incorrect in this case
-- because the branch does not dominate the mux.  However, this would work with
-- a merge instead, where there is no direct connection.
namespace INCORRECT

def matchModLeft' (g : ExprHigh String) : RewriteResult (List String) := do
  let dom ← ofOption (.error "could not calculate dominators") <| findDom 10000 g
  let muxes := g.modules.filter (λ k v => v.snd = "mux") |>.toList |>.map (·.fst)
  let branches := g.modules.filter (λ k v => v.snd = "branch") |>.toList |>.map (·.fst)
  let (.some pair) ← muxes.foldlM (λ s x => do
      if s.isSome then return s
      let br ← ofOption (.error "mux node not in dominators") dom[x]?
      unless br ∈ branches do return none
      return some (br, x)
    ) none | throw .done
  let (.some nn_first) := followOutput g pair.fst "true" | throw (.error "could not follow output")
  let (.some nn_last) := followInput g pair.snd "inp0" | throw (.error "could not follow input")
  ofOption (.error "could not find scc nodes") <| findSCCNodes g nn_first.inst nn_last.inst

/--
We can use dominators to make sure we match the same nodes as in the two
previous functions.  This doesn't work in this case though because of the fork.
If the mux were a merge domination would be the right algorithm.
-/
def matcher' (g : ExprHigh String) : RewriteResult (List String) := do
  let dom ← ofOption (.error "could not calculate dominators") <| findDom 10000 g
  let muxes := g.modules.filter (λ k v => v.snd = "mux") |>.toList |>.map (·.fst)
  let branches := g.modules.filter (λ k v => v.snd = "branch") |>.toList |>.map (·.fst)
  let (.some pair) ← muxes.foldlM (λ s x => do
      if s.isSome then return s
      let br ← ofOption (.error "mux node not in dominators") dom[x]?
      unless br ∈ branches do return none
      return some (br, x)
    ) none | throw .done
  ofOption (.error "could not find scc nodes") <| findSCCNodes g pair.fst pair.snd

end INCORRECT

/--
Match the left module so that it can be abstracted.
-/
def matchModLeft (g : ExprHigh String) : RewriteResult (List String) := do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
      if s.isSome then return s
      unless typ = "fork" do return none
      let (.some branch_nn) := followOutput g inst "out0" | return none
      unless branch_nn.typ = "branch" && branch_nn.inputPort = "cond" do return none
      let (.some mux_nn) := followOutput g inst "out1" | return none
      unless mux_nn.typ = "mux" && mux_nn.inputPort = "cond" do return none
      let (.some prev_mux_nn) := followInput g inst "inp0" | return none
      let (.some after_branch_nn) := followOutput g inst "true" | return none
      let (.some scc) := findSCCNodes g after_branch_nn.inst prev_mux_nn.inst | return none
      return some (inst :: scc)
    ) none | throw .done
  return list

/--
Match the right module so that it can be abstracted.
-/
def matchModRight (g : ExprHigh String) : RewriteResult (List String) := do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
      if s.isSome then return s
      unless typ = "fork" do return none
      let (.some branch_nn) := followOutput g inst "out0" | return none
      unless branch_nn.typ = "branch" && branch_nn.inputPort = "cond" do return none
      let (.some mux_nn) := followOutput g inst "out1" | return none
      unless mux_nn.typ = "mux" && mux_nn.inputPort = "cond" do return none
      let (.some prev_mux_nn) := followInput g inst "inp1" | return none
      let (.some after_branch_nn) := followOutput g inst "false" | return none
      let (.some scc) := findSCCNodes g after_branch_nn.inst prev_mux_nn.inst | return none
      return some (inst :: scc)
    ) none | throw .done
  return list

/--
Instead of using dominators we can also use the fork and the condition circuit
to match the graph.
-/
def matcher (g : ExprHigh String) : RewriteResult (List String) := do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
      if s.isSome then return s
      unless typ = "fork" do return none
      let (.some branch_nn) := followOutput g inst "out0" | return none
      unless branch_nn.typ = "branch" && branch_nn.inputPort = "cond" do return none
      let (.some mux_nn) := followOutput g inst "out1" | return none
      unless mux_nn.typ = "mux" && mux_nn.inputPort = "cond" do return none
      let (.some scc) := findSCCNodes g branch_nn.inst mux_nn.inst | return none
      return some (inst :: scc)
    ) none | throw .done
  return list

def lhs' : ExprHigh String := [graph|
    i_branch [mod = "io"];
    i_cond [mod = "io"];
    o_out [mod = "io"];

    branch [mod = "branch"];
    m_left [mod = "mod_left"];
    m_right [mod = "mod_right"];
    mux [mod = "mux"];
    fork [mod = "fork"];

    i_branch -> branch [inp = "val"];
    i_cond -> fork [inp = "inp0"];
    fork -> branch [out = "out0", inp = "cond"];
    fork -> mux [out = "out1", inp = "cond"];

    mux -> o_out [out = "out0"];

    branch -> m_left [out = "true", inp = "m_in"];
    branch -> m_right [out = "false", inp = "m_in"];

    m_left -> mux [out = "m_out", inp = "inp0"];
    m_right -> mux [out = "m_out", inp = "inp1"];
  ]

#eval IO.print lhs'

def lhs := lhs'.extract ["fork", "m_left", "mux", "m_right", "branch"] |>.get rfl

theorem double_check_empty_snd : lhs.snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := lhs.fst.lower.get rfl

def rhs : ExprHigh String := [graph|
    i_branch [mod = "io"];
    i_cond [mod = "io"];
    o_out [mod = "io"];

    branch [mod = "branch"];
    m_left [mod = "mod_left"];
    m_right [mod = "mod_right"];
    merge [mod = "merge"];

    i_branch -> branch [inp = "val"];
    i_cond -> branch [inp = "cond"];

    merge -> o_out [out = "out"];

    branch -> m_left [out = "true", inp = "m_in"];
    branch -> m_right [out = "false", inp = "m_in"];

    m_left -> merge [out = "m_out", inp = "inp0"];
    m_right -> merge [out = "m_out", inp = "inp1"];
  ]

#eval IO.print rhs

def rhsLower := rhs.lower.get rfl

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

end DataflowRewriter.BranchMuxToMerge