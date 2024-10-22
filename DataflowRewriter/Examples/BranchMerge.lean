/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.Module
import DataflowRewriter.Component
import DataflowRewriter.ExprHigh

namespace DataflowRewriter

section BranchMerge

  @[simp]
  def queue T : Module (List T) :=
   { inputs := [⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩],
     outputs := [⟨ T, λ oldList oldElement newList =>  newList ++ [oldElement] = oldList ⟩],
     internals := []
  }

  @[simp]
  def merger T R : Module (List T × List R) :=
   { inputs := [⟨ T, λ (oldListT,oldListR) newElementT (newListT, newListR) => newListT = newElementT ::  oldListT ∧ newListR = oldListR ⟩,
                ⟨ R, λ (oldListT,oldListR) newElementR (newListT, newListR) => newListR = newElementR ::  oldListR ∧ newListT = oldListT ⟩,
   ],
     outputs := [⟨ T × R , λ (oldListT,oldListR) (elementT, elementR) (newListT, newListR) =>
       newListT ++ [elementT] = oldListT ∧
       newListR ++ [elementR] = oldListR
        ⟩],
     internals := []}

  @[simp]
  def pipelined_m TagT (m : Module Q) (wf :  m.outputs.length = 1) :=
    merge_outputs (product m (queue TagT)) ⟨0, by simp⟩  ⟨1, by simp; omega⟩

  -- We should start thinking about moving things in component libraries
  @[simp]
  def bag T : Module (List T) :=
        { inputs := [⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩],
          outputs := [⟨ T, λ oldList oldElement newList => ∃ i, newList = oldList.remove i ∧ oldElement = oldList.get i ⟩],
          internals := []}
  -- set_option trace.profiler true
  @[simp]
  def bagged_m (Q: Type _) (TagT : Type _) (m : Module Q) (wf :  m.outputs.length = 1 ∧ m.inputs.length = 1) :=
    let pipe := pipelined_m TagT m wf.1;
    let prod := product pipe (bag (m.outputs[0].1 × TagT));
    connect prod ⟨2, by sorry⟩ ⟨0, by sorry⟩ (by sorry)

  @[simp]
  def bagged : ExprHigh :=
  [graph|
      pipe [mod="pipe"];
      bag [mod="bag"];
      pipe -> bag [inp = 2, out = 0];
  ]

  def baggedl : ExprLow :=  Option.get (lower [("pipe", ⟨2,1⟩), ("bag", ⟨1,1⟩)].toAssocList bagged) rfl

  def bagged_m' (Q: Type _) (TagT : Type 0) (m : Module Q) (wf : m.outputs.length = 1 ∧ m.inputs.length = 1) := do
      build_module' baggedl [("pipe", (⟨_, pipelined_m TagT m wf.1⟩ : ((T: Type _) × Module T))),
                             ("bag", ⟨_, bag (m.outputs[0].1 × TagT)⟩)].toAssocList

  @[simp]
  def tag_complete_spec (TagT : Type 0) [_i: BEq TagT] (T : Type 0) : Module (List TagT × (TagT → Option T)) :=
        { inputs := [
          -- Complete computation
          ⟨ TagT × T, λ (oldOrder, oldMap) (tag,el) (newOrder, newMap) =>
            -- Tag must be used, but no value ready, otherwise block:
            (List.elem tag oldOrder ∧ oldMap tag = none) ∧
            newMap = (λ idx => if idx == tag then some el else oldMap idx) ∧ newOrder = oldOrder⟩
        ],
          outputs := [
            -- Allocate fresh tag
          ⟨ TagT, λ (oldOrder, oldMap) (tag) (newOrder, newMap) =>
            -- Tag must be unused otherwise block (alternatively we
            -- could an implication to say undefined behavior):
            (!List.elem tag oldOrder ∧ oldMap tag = none) ∧
            newMap = oldMap ∧ newOrder = tag :: oldOrder⟩,
            -- Dequeue + free tag
          ⟨ T, λ (oldorder, oldmap) el (neworder, newmap) =>
            -- tag must be used otherwise, but no value brought, undefined behavior:
            ∃ l tag , oldorder = l ++ [tag] ∧ oldmap tag = some el ∧
            newmap = (λ idx => if idx == tag then none else oldmap idx) ∧ neworder = l ⟩,
            ],
          internals := []}

  @[simp]
  def tagged_ooo_h : ExprHigh :=
  [graph|
      tagger [mod="tag"];
      bagged [mod="bag"];
      merger [mod="merge"];
      -- Match tag and input
      tagger -> merger [inp = 0, out = 0];
      -- Feed the pair to the bag
      merger -> bagged [inp = 0, out = 0];
      -- Output of the bag complete inside the tagger
      bagged -> tagger [inp = 0, out = 0];

      -- Top-level inputs: The second input to merger which is unbound
      -- Top-level outputs: Second output of the tagger which is unbound
    ]

  @[simp]
  def tagged_ooo_l : ExprLow :=  Option.get (lower [("tag", ⟨1,2⟩), ("bag", ⟨1,1⟩), ("merge", ⟨2,1⟩)].toAssocList tagged_ooo_h) (Eq.refl _)

end BranchMerge

end DataflowRewriter
