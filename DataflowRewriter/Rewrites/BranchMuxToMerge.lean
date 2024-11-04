/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.Rewriter
import DataflowRewriter.ExprHighElaborator
import DataflowRewriter.KernelRefl

namespace DataflowRewriter.BranchMuxToMerge

def matchModLeft (g : ExprHigh String) : RewriteResult (List String) := do
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

def matchModRight (g : ExprHigh String) : RewriteResult (List String) := do
  let dom ← ofOption (.error "could not calculate dominators") <| findDom 10000 g
  let muxes := g.modules.filter (λ k v => v.snd = "mux") |>.toList |>.map (·.fst)
  let branches := g.modules.filter (λ k v => v.snd = "branch") |>.toList |>.map (·.fst)
  let (.some pair) ← muxes.foldlM (λ s x => do
      if s.isSome then return s
      let br ← ofOption (.error "mux node not in dominators") dom[x]?
      unless br ∈ branches do return none
      return some (br, x)
    ) none | throw .done
  let (.some nn_first) := followOutput g pair.fst "false" | throw (.error "could not follow output")
  let (.some nn_last) := followInput g pair.snd "inp1" | throw (.error "could not follow input")
  ofOption (.error "could not find scc nodes") <| findSCCNodes g nn_first.inst nn_last.inst

def matcher (g : ExprHigh String) : RewriteResult (List String) := do
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

def lhs' : ExprHigh String := [graph|
    i_branch [mod = "io"];
    i_cond [mod = "io"];
    o_out [mod = "io"];

    branch [mod = "branch"];
    m_left [mod = "mod_left"];
    m_right [mod = "mod_right"];
    mux [mod = "mux"];

    i_branch -> branch [inp = "val"];
    i_cond -> branch [inp = "cond"];

    mux -> o_out [out = "out"];

    branch -> m_left [out = "true", inp = "m_in"];
    branch -> m_right [out = "false", inp = "m_in"];

    m_left -> mux [out = "m_out", inp = "inp0"];
    m_right -> mux [out = "m_out", inp = "inp1"];
  ]

def lhs := lhs'.extract ["m_left", "mux", "m_right", "branch"] |>.get rfl

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

def rhsLower := rhs.lower.get rfl

def rewrite : Rewrite String :=
  { abstractions := [⟨matchModLeft, "mod_left"⟩, ⟨matchModRight, "mod_right"⟩],
    pattern := matcher,
    input_expr := lhsLower,
    output_expr := rhsLower }

end DataflowRewriter.BranchMuxToMerge
