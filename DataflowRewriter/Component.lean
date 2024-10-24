/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.Module
import DataflowRewriter.Simp
import DataflowRewriter.ExprHigh

namespace DataflowRewriter.NatModule

@[drunfold] def io (T : Type) : NatModule (List T) :=
  { inputs := [(0, ⟨ T, λ s tt s' => s' = tt :: s ⟩)].toAssocList,
    internals := [],
    outputs := [(0, ⟨ T, λ s tt s' => s = s' ++ [tt] ⟩)].toAssocList
  }

@[drunfold] def merge_inputs {S} (mod : NatModule S) (in1 in2 : InternalPort Nat) : Option (NatModule S)  := do
  let in1_t ← mod.inputs.find? in1;
  let in2_t ← mod.inputs.find? in2;
  let rmin2 := mod.inputs.erase in2;
  some { inputs :=
         rmin2.cons in2 ⟨ in1_t.1 × in2_t.1, λ s (v1,v2) s' =>
               ∃ s_int, in1_t.2 s v1 s_int ∧
               in2_t.2 s_int v2 s'⟩,
         outputs := mod.outputs,
         internals := mod.internals }

@[drunfold] def merge_outputs {S} (mod : NatModule S) (out1 out2 : InternalPort Nat) : Option (NatModule S)  := do
  let out1_t ← mod.outputs.find? out1;
  let out2_t ← mod.outputs.find? out2;
  let rmout2 := mod.outputs.erase out2;
      some { outputs :=
               rmout2.cons out2 ⟨ out1_t.1 × out2_t.1, λ s (v1,v2) s' =>
                   ∃ s_int, out1_t.2 s v1 s_int ∧
                   out2_t.2 s_int v2 s' ⟩,
             inputs := mod.inputs,
             internals := mod.internals }

@[drunfold] def merge T : NatModule (List T) :=
      { inputs := [(0, ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩),
                   (1, ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩)].toAssocList,
        outputs := [(0, ⟨ T, λ oldList oldElement newList =>
                           ∃ i, newList = oldList.remove i
                             ∧ oldElement = oldList.get i ⟩)].toAssocList,
        internals := []
      }

@[drunfold] def fork T : NatModule (List T) :=
      { inputs := [(0, ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩)].toAssocList,
        outputs := [ (0, ⟨ T, λ oldList oldElement newList => ∃ i, newList = oldList.remove i ∧ oldElement = oldList.get i ⟩)
                   , (1, ⟨ T, λ oldList oldElement newList => ∃ i, newList = oldList.remove i ∧ oldElement = oldList.get i ⟩)
                   ].toAssocList,
        internals := []
      }

@[drunfold] def queue T : NatModule (List T) :=
   { inputs := [( ⟨ .top, 0⟩ ,⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩)].toAssocList,
     outputs := [(⟨ .top, 0⟩, ⟨ T, λ oldList oldElement newList =>  newList ++ [oldElement] = oldList ⟩)].toAssocList,
     internals := []
  }
@[drunfold] def queueS T : StringModule (List T) :=
       queue T |>.mapIdent (λ x => "enq") (λ x => "deq")

@[drunfold] def join T T' : NatModule (List T× List T') :=
      { inputs := [ (0, ⟨ T, λ (oldListL,oldListR) newElement (newListL,newListR) =>
                           newListL = newElement :: oldListL ∧ newListR = oldListR⟩)
                  , (1, ⟨ T', λ (oldListL,oldListR) newElement (newListL,newListR) =>
                           newListR = newElement :: oldListR ∧ newListL = oldListL⟩)].toAssocList,
        outputs := [(0, ⟨ T, λ (oldListL,oldListR) oldElement (newListL,newListR) =>
                           ∃ hL hR, oldListL = hL :: newListL ∧
                                    oldListR = hR :: newListR ⟩)].toAssocList,
        internals := []
      }

@[drunfold] def bag T : NatModule (List T) :=
        { inputs := [(0,⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩)].toAssocList,
          outputs := [(0,⟨ T, λ oldList oldElement newList => ∃ i, newList = oldList.remove i ∧ oldElement = oldList.get i ⟩)].toAssocList,
          internals := []}

@[drunfold] def tag_complete_spec (TagT : Type 0) [_i: DecidableEq TagT] (T : Type 0) : NatModule (List TagT × (TagT → Option T)) :=
  { inputs := [
        -- Complete computation
        (0,⟨ TagT × T, λ (oldOrder, oldMap) (tag,el) (newOrder, newMap) =>
          -- Tag must be used, but no value ready, otherwise block:
          (List.elem tag oldOrder ∧ oldMap tag = none) ∧
          newMap = (λ idx => if idx == tag then some el else oldMap idx) ∧ newOrder = oldOrder⟩)
      ].toAssocList,
    outputs := [
        -- Allocate fresh tag
      (0,⟨ TagT, λ (oldOrder, oldMap) (tag) (newOrder, newMap) =>
        -- Tag must be unused otherwise block (alternatively we
        -- could an implication to say undefined behavior):
        (!List.elem tag oldOrder ∧ oldMap tag = none) ∧
        newMap = oldMap ∧ newOrder = tag :: oldOrder⟩),
        -- Dequeue + free tag
      (1,⟨ T, λ (oldorder, oldmap) el (neworder, newmap) =>
        -- tag must be used otherwise, but no value brought, undefined behavior:
        ∃ l tag , oldorder = l ++ [tag] ∧ oldmap tag = some el ∧
        newmap = (λ idx => if idx == tag then none else oldmap idx) ∧ neworder = l ⟩),
        ].toAssocList,
    internals := []
  }

end DataflowRewriter.NatModule

namespace DataflowRewriter.StringModule

@[drunfold] def bagS T : StringModule (List T) :=
  NatModule.bag T |>.mapIdent (λ x => "enq") (λ x => "deq")

end DataflowRewriter.StringModule
