/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.Module
import DataflowRewriter.Simp
import DataflowRewriter.ExprHigh
import DataflowRewriter.AssocList.Basic

open Batteries (AssocList)

namespace DataflowRewriter.NatModule

@[drunfold] def io (T : Type) : NatModule (List T) :=
  { inputs := [(0, ⟨ T, λ s tt s' => s' = tt :: s ⟩)].toAssocList,
    internals := [],
    outputs := [(0, ⟨ T, λ s tt s' => s = s'.concat tt ⟩)].toAssocList
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

@[drunfold] def merge T (n : Nat) : NatModule (List T) :=
  { inputs := List.range n |>.map (Prod.mk ↑· (⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩)) |>.toAssocList,
    outputs := [(0, ⟨ T, λ oldList oldElement newList =>
                       ∃ i, newList = oldList.remove i
                         ∧ oldElement = oldList.get i ⟩)].toAssocList,
    internals := []
  }

@[drunfold] def fork T (n : Nat) : NatModule (List T) :=
  { inputs := [(0, ⟨ T, λ oldList newElement newList => newList = oldList.concat newElement ⟩)].toAssocList,
    outputs := List.range n |>.map (Prod.mk ↑· ⟨ T, λ oldList oldElement newList => oldElement :: newList = oldList⟩) |>.toAssocList,
    internals := []
  }

@[drunfold] def fork2 T : NatModule (List T × List T) :=
  { inputs := [(0, ⟨ T, λ (oldListL, oldListR) newElement (newListL, newListR)=> newListR = oldListR.concat newElement ∧ newListL = oldListL.concat newElement ⟩)].toAssocList,
    outputs := [(0, ⟨ T, λ (oldListL, oldListR) oldElement (newListL, newListR) => oldElement :: newListL = oldListL ∧ newListR = oldListR ⟩), (1, ⟨ T, λ (oldListL, oldListR) oldElement (newListL, newListR) => oldElement :: newListR = oldListR ∧ newListL = oldListL ⟩)] |>.toAssocList,
    internals := []
  }

@[drunfold] def queue T : NatModule (List T) :=
  { inputs := [(⟨ .top, 0 ⟩, ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩)].toAssocList,
    outputs := [(⟨ .top, 0 ⟩, ⟨ T, λ oldList oldElement newList =>  newList.concat oldElement = oldList ⟩)].toAssocList,
    internals := []
  }

@[drunfold] def join T T' : NatModule (List T × List T') :=
  { inputs := [ (0, ⟨ T, λ (oldListL, oldListR) newElement (newListL, newListR) =>
                       newListL = oldListL.concat newElement ∧ newListR = oldListR⟩)
              , (1, ⟨ T', λ (oldListL, oldListR) newElement (newListL, newListR) =>
                       newListR = oldListR.concat newElement ∧ newListL = oldListL⟩)].toAssocList,
    outputs := [(0, ⟨ T × T', λ (oldListL, oldListR) (oldElementL, oldElementR) (newListL, newListR) =>
                       oldListL = oldElementL :: newListL ∧
                       oldListR = oldElementR :: newListR ⟩)].toAssocList,
    internals := []
  }

@[drunfold] def branch T : NatModule (List T × List Bool) :=
  { inputs := [ (0, ⟨ T, λ (oldValList, oldBoolList) val (newValList, newBoolList) =>
                           newValList = val :: oldValList ∧ newBoolList = oldBoolList ⟩)
              , (1, ⟨ Bool, λ (oldValList, oldBoolList) b (newValList, newBoolList) =>
                           newValList = oldValList ∧ newBoolList = b :: oldBoolList ⟩)
              ].toAssocList
    outputs := [ (0, ⟨ T, λ (oldValList, oldBoolList) val (newValList, newBoolList) =>
                            newValList.concat val = oldValList ∧ newBoolList.concat true = oldBoolList ⟩)
               , (1, ⟨ T, λ (oldValList, oldBoolList) val (newValList, newBoolList) =>
                            newValList.concat val = oldValList ∧ newBoolList.concat false = oldBoolList ⟩)
               ].toAssocList
    internals := []
  }

@[drunfold] def mux T : NatModule (List T × List T × List Bool) :=
  { inputs := [ (0, ⟨ T, λ (oldTrueList, oldFalseList, oldBoolList) val (newTrueList, newFalseList, newBoolList) =>
                           newTrueList = oldTrueList.concat val ∧ newFalseList = oldFalseList ∧ newBoolList = oldBoolList ⟩)
              , (1, ⟨ T, λ (oldTrueList, oldFalseList, oldBoolList) val (newTrueList, newFalseList, newBoolList) =>
                           newTrueList = oldTrueList ∧ newFalseList = oldFalseList.concat val ∧ newBoolList = oldBoolList ⟩)
              , (2, ⟨ Bool, λ (oldTrueList, oldFalseList, oldBoolList) b (newTrueList, newFalseList, newBoolList) =>
                           newTrueList = oldTrueList ∧ newFalseList = oldFalseList ∧ newBoolList = oldBoolList.concat b ⟩)
              ].toAssocList
    outputs := [ (0, ⟨ T, λ (oldTrueList, oldFalseList, oldBoolList) val (newTrueList, newFalseList, newBoolList) =>
                            ∃ b, b :: newBoolList = oldBoolList
                              ∧ if b then val :: newTrueList = oldTrueList ∧ newFalseList = oldFalseList
                                     else newTrueList = oldTrueList ∧ val :: newFalseList = oldFalseList ⟩)
               ].toAssocList
    internals := []
  }

@[drunfold] def muxC T : NatModule (List T × List T × List Bool) :=
  { inputs := [ (0, ⟨ T, λ (oldTrueList, oldFalseList, oldBoolList) val (newTrueList, newFalseList, newBoolList) =>
                           newTrueList = oldTrueList.concat val ∧ newFalseList = oldFalseList ∧ newBoolList = oldBoolList ⟩)
              , (1, ⟨ T, λ (oldTrueList, oldFalseList, oldBoolList) val (newTrueList, newFalseList, newBoolList) =>
                           newTrueList = oldTrueList ∧ newFalseList = oldFalseList.concat val ∧ newBoolList = oldBoolList ⟩)
              , (2, ⟨ Bool, λ (oldTrueList, oldFalseList, oldBoolList) b (newTrueList, newFalseList, newBoolList) =>
                           newTrueList = oldTrueList ∧ newFalseList = oldFalseList ∧ newBoolList = oldBoolList.concat b ⟩)
              ].toAssocList
    outputs := [ (0, ⟨ T×Bool, λ (oldTrueList, oldFalseList, oldBoolList) (val, b) (newTrueList, newFalseList, newBoolList) =>
                            b :: newBoolList = oldBoolList
                              ∧ if b then val :: newTrueList = oldTrueList ∧ newFalseList = oldFalseList
                                     else newTrueList = oldTrueList ∧ val :: newFalseList = oldFalseList ⟩)
               ].toAssocList
    internals := []
  }


@[drunfold] def joinC T T' T'' : NatModule (List T × List (T'× T'')) :=
  { inputs := [ (0, ⟨ T, λ (oldListL, oldListR) newElement (newListL, newListR) =>
                       newListL = oldListL.concat newElement ∧ newListR = oldListR⟩)
              , (1, ⟨ T' × T'', λ (oldListL, oldListR) newElement (newListL, newListR) =>
                       newListR = oldListR.concat newElement ∧ newListL = oldListL⟩)].toAssocList,
    outputs := [(0, ⟨ T × T', λ (oldListL, oldListR) (oldElementL, oldElementR) (newListL, newListR) =>
                       ∃ x, oldListL =  oldElementL :: newListL ∧
                       oldListR = (oldElementR, x) :: newListR ⟩)].toAssocList,
    internals := []
  }
@[drunfold] def bag T : NatModule (List T) :=
  { inputs := [(0,⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩)].toAssocList,
    outputs := [(0,⟨ T, λ oldList oldElement newList => ∃ i, newList = oldList.remove i ∧ oldElement = oldList.get i ⟩)].toAssocList,
    internals := []}

@[drunfold] def tagger_untagger (TagT : Type 0) [_i: DecidableEq TagT] (T : Type 0) : NatModule (List TagT × (AssocList TagT T)) :=
  { inputs := [
        -- Complete computation
        (0, ⟨ TagT × T, λ (oldOrder, oldMap) (tag,el) (newOrder, newMap) =>
          -- Tag must be used, but no value ready, otherwise block:
          (tag ∈ oldOrder ∧ oldMap.find? tag = none) ∧
          newMap = oldMap.cons tag el ∧ newOrder = oldOrder⟩)
      ].toAssocList,
    outputs := [
        -- Allocate fresh tag
      (0, ⟨ TagT, λ (oldOrder, oldMap) (tag) (newOrder, newMap) =>
        -- Tag must be unused otherwise block (alternatively we
        -- could an implication to say undefined behavior):
        (tag ∉ oldOrder ∧ oldMap.find? tag = none) ∧
        newMap = oldMap ∧ newOrder = tag :: oldOrder⟩),
        -- Dequeue + free tag
      (1, ⟨ T, λ (oldorder, oldmap) el (neworder, newmap) =>
        -- tag must be used otherwise, but no value brought, undefined behavior:
        ∃ l tag , oldorder = l.cons tag ∧ oldmap.find? tag = some el ∧
        newmap = oldmap.eraseAll tag ∧ neworder = l ⟩),
        ].toAssocList,
    internals := []
  }

/--
Essentially tagger + join without internal rule
-/
@[drunfold] def tagger_untagger_val (TagT : Type 0) [_i: DecidableEq TagT] (T : Type 0) : NatModule (List TagT × AssocList TagT T × List T) :=
  { inputs := [
        -- Complete computation
        (0, ⟨ TagT × T, λ (oldOrder, oldMap, oldVal) (tag,el) (newOrder, newMap, newVal) =>
          -- Tag must be used, but no value ready, otherwise block:
          (tag ∈ oldOrder ∧ oldMap.find? tag = none) ∧
          newMap = oldMap.cons tag el ∧ newOrder = oldOrder ∧ newVal = oldVal ⟩),
        -- Enq a value to be tagged
        (0, ⟨ T, λ (oldOrder, oldMap, oldVal) v (newOrder, newMap, newVal) =>
          -- Tag must be used, but no value ready, otherwise block:
          newMap = oldMap ∧ newOrder = oldOrder ∧ newVal = v :: oldVal ⟩)
      ].toAssocList,
    outputs := [
        -- Allocate fresh tag and output with value
      (0, ⟨ TagT × T, λ (oldOrder, oldMap, oldVal) (tag, v) (newOrder, newMap, newVal) =>
        -- Tag must be unused otherwise block (alternatively we
        -- could an implication to say undefined behavior):
        (tag ∉ oldOrder ∧ oldMap.find? tag = none) ∧
        newMap = oldMap ∧ newOrder = tag :: oldOrder ∧ newVal.cons v = oldVal⟩),
        -- Dequeue + free tag
      (1, ⟨ T, λ (oldorder, oldmap, oldVal) el (neworder, newmap, newVal) =>
        -- tag must be used otherwise, but no value brought, undefined behavior:
        ∃ l tag , oldorder = l.cons tag ∧ oldmap.find? tag = some el ∧
        newmap = oldmap.eraseAll tag ∧ neworder = l ∧ newVal = oldVal ⟩),
        ].toAssocList,
    internals := []
  }

@[drunfold] def tagger (TagT : Type) [DecidableEq TagT] T : NatModule (List (TagT × T) × List TagT) :=
  { inputs := [
        -- Allocate tag
        (0, ⟨ T, λ (oldEl, oldOrder) el (newEl, newOrder) =>
          ∃ tag, tag ∉ oldOrder ∧ newEl = (tag, el) :: oldEl ∧ newOrder = tag :: oldOrder ⟩),
        -- Free tag
        (1, ⟨ TagT, λ (oldEl, oldOrder) t (newEl, newOrder) =>
          newOrder = oldOrder.erase t ∧ newEl = oldEl ⟩)
      ].toAssocList,
    outputs := [
        (0, ⟨ TagT × T, λ (oldEl, oldOrder) el (newEl, newOrder) =>
          newEl.concat el = oldEl ∧ newOrder = oldOrder⟩)
      ].toAssocList,
    internals := []
  }

namespace FixedSize

def BoundedList T n := { ls : List T // ls.length <= n }

@[drunfold] def join T T' n : NatModule (BoundedList T n × BoundedList T' n) :=
  { inputs := [ (0, ⟨ T, λ (oldListL, oldListR) newElement (newListL, newListR) =>
                      newListL.val = newElement :: oldListL.val ∧ newListR = oldListR ⟩)
              , (1, ⟨ T', λ (oldListL, oldListR) newElement (newListL, newListR) =>
                      newListR.val = newElement :: oldListR.val ∧ newListL = oldListL⟩)].toAssocList,
    outputs := [(0, ⟨ T × T', λ (oldListL, oldListR) (oldElementL, oldElementR) (newListL, newListR) =>
                         oldListL.val = newListL.val.concat oldElementL
                         ∧ oldListR.val = newListR.val.concat oldElementR ⟩)].toAssocList,
    internals := []
  }

@[drunfold] def joinL T T' T'' n : NatModule (BoundedList (T × T') n × BoundedList T'' n) :=
  { inputs := [ (0, ⟨ T × T', λ (oldListL, oldListR) newElement (newListL, newListR) =>
                      newListL.val = newElement :: oldListL.val ∧ newListR = oldListR ⟩)
              , (1, ⟨ T'', λ (oldListL, oldListR) newElement (newListL, newListR) =>
                      newListR.val = newElement :: oldListR.val ∧ newListL = oldListL⟩)].toAssocList,
    outputs := [(0, ⟨ T × T' × T'', λ (oldListL, oldListR)  (oldElementL₁, oldElementL₂, oldElementR) (newListL, newListR) =>
                        oldListL.val = newListL.val.concat (oldElementL₁, oldElementL₂)
                         ∧ oldListR.val = newListR.val.concat oldElementR⟩)].toAssocList,
    internals := []
  }


end FixedSize

end DataflowRewriter.NatModule

namespace DataflowRewriter.StringModule

@[drunfold] def bag T : StringModule (List T) :=
  NatModule.bag T |>.mapIdent (λ x => "enq") (λ x => "deq")

@[drunfold] def merge T n := NatModule.merge T n |>.stringify

@[drunfold] def fork T n := NatModule.fork T n |>.stringify

@[drunfold] def fork2 T := NatModule.fork2 T|>.stringify

@[drunfold] def queue T : StringModule (List T) :=
  NatModule.queue T |>.mapIdent (λ x => "enq") (λ x => "deq")

@[drunfold] def join T T' := NatModule.join T T' |>.stringify

@[drunfold] def branch T := NatModule.branch T
  |>.mapIdent (λ | 0 => "val" | _ => "cond") (λ | 0 => "true" | _ => "false")

@[drunfold] def mux T := NatModule.mux T
  |>.stringify

@[drunfold] def tagger TagT [DecidableEq TagT] T := NatModule.tagger TagT T

@[drunfold] def muxC T := NatModule.muxC T
  |>.stringify

@[drunfold] def joinC T T' T'' := NatModule.joinC T T' T'' |>.stringify

namespace FixedSize

@[drunfold] def join T T' n := NatModule.FixedSize.join T T' n |>.stringify

@[drunfold] def joinL T T' T'' n := NatModule.FixedSize.joinL T T' T'' n |>.stringify

end FixedSize
end DataflowRewriter.StringModule
