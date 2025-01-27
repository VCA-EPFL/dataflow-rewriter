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
  { inputs := [(0, ⟨ T, λ s tt s' => s' = s.concat tt ⟩)].toAssocList,
    outputs := [(0, ⟨ T, λ s tt s' => s = tt :: s' ⟩)].toAssocList
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
                         ∧ oldElement = oldList.get i ⟩)].toAssocList
  }

@[drunfold] def cntrl_merge T : NatModule (List T × List Bool) :=
  { inputs := [ (0, ⟨ T, λ (oldListL, oldListR) newElement (newListL, newListR) =>
                    newListL = oldListL.concat newElement ∧ newListR = oldListR.concat true ⟩)
              , (1, ⟨ T, λ (oldListL, oldListR) newElement (newListL, newListR) =>
                    newListL = oldListL.concat newElement ∧ newListR = oldListR.concat false ⟩)
              ].toAssocList,
    outputs := [ (0, ⟨ T, λ (oldListL, oldListR) oldElement (newListL, newListR) =>
                    oldElement :: newListL = oldListL ∧ newListR = oldListR ⟩)
               , (1, ⟨ Bool, λ (oldListL, oldListR) oldElement (newListL, newListR) =>
                    oldElement :: newListR = oldListR ∧ newListL = oldListL ⟩)
               ].toAssocList
  }

@[drunfold] def cntrl_merge_n T (n : Nat) : NatModule (List T × List Nat) :=
  { inputs := List.range n |>.map (Prod.mk ↑· (⟨ T, λ (oldListL, oldListR) newElement (newListL, newListR) =>
                newListL = oldListL.concat newElement ∧ newListR = oldListR.concat n ⟩)) |>.toAssocList,
    outputs := [ (0, ⟨ T, λ (oldListL, oldListR) oldElement (newListL, newListR) =>
                       oldElement :: newListL = oldListL ∧ newListR = oldListR ⟩)
               , (1, ⟨ Nat, λ (oldListL, oldListR) oldElement (newListL, newListR) =>
                       oldElement :: newListR = oldListR ∧ newListL = oldListL ⟩)
               ].toAssocList
  }

@[drunfold] def fork T (n : Nat) : NatModule (List T) :=
  { inputs := [(0, ⟨ T, λ oldList newElement newList => newList = oldList.concat newElement ⟩)].toAssocList,
    outputs := List.range n |>.map (Prod.mk ↑· ⟨ T, λ oldList oldElement newList => oldElement :: newList = oldList⟩) |>.toAssocList
  }

@[drunfold] def fork2 T : NatModule (List T × List T) :=
  { inputs := [(0, ⟨ T, λ (oldListL, oldListR) newElement (newListL, newListR)=> newListR = oldListR.concat newElement ∧ newListL = oldListL.concat newElement ⟩)].toAssocList,
    outputs := [(0, ⟨ T, λ (oldListL, oldListR) oldElement (newListL, newListR) => oldElement :: newListL = oldListL ∧ newListR = oldListR ⟩), (1, ⟨ T, λ (oldListL, oldListR) oldElement (newListL, newListR) => oldElement :: newListR = oldListR ∧ newListL = oldListL ⟩)] |>.toAssocList
  }

def push_n {T} (n : Nat) (l : List (List T)) (t : T) : Option (List (List T)) :=
  List.range n |>.foldlM (λ m i => l.get? i >>= λ l' => m.set i (l'.concat t)) (List.replicate n [])

def cons_n {T} (n : Nat) (l : List (List T)) (t : T) : Option (List (List T)) :=
  l.get? n >>= λ l' => l.set n (t :: l')

@[drunfold] def forkN T (n : Nat) : NatModule (List (List T)) :=
  { inputs := [(0, ⟨ T, λ ol el nl => .some nl = push_n n ol el ⟩)].toAssocList,
    outputs := List.range n |>.map (
        λ ind => (↑ind, ⟨ T, λ ol el nl =>
          .some ol = cons_n ind nl el
      ⟩)) |>.toAssocList
  }

@[drunfold] def queue T : NatModule (List T) :=
  { inputs := [(⟨ .top, 0 ⟩, ⟨ T, λ oldList newElement newList => newList = oldList.concat newElement ⟩)].toAssocList,
    outputs := [(⟨ .top, 0 ⟩, ⟨ T, λ oldList oldElement newList =>  oldElement :: newList = oldList ⟩)].toAssocList
  }

@[drunfold] def init T (default : T) : NatModule (List T × Bool) :=
  { inputs := [(⟨ .top, 0 ⟩, ⟨ T, λ (oldList, oldState) newElement (newList, newState) =>
      newList = oldList.concat newElement ∧ oldState = newState ⟩)].toAssocList,
    outputs := [(⟨ .top, 0 ⟩, ⟨ T, λ (oldList, oldState) oldElement (newList, newState) =>
      if oldState then
        oldElement :: newList = oldList ∧ oldState = newState
      else
        newList = oldList ∧ newState = true ∧ oldElement = default ⟩)].toAssocList
  }

@[drunfold] def join T T' : NatModule (List T × List T') :=
  { inputs := [ (0, ⟨ T, λ (oldListL, oldListR) newElement (newListL, newListR) =>
                       newListL = oldListL.concat newElement ∧ newListR = oldListR⟩)
              , (1, ⟨ T', λ (oldListL, oldListR) newElement (newListL, newListR) =>
                       newListR = oldListR.concat newElement ∧ newListL = oldListL⟩)].toAssocList,
    outputs := [(0, ⟨ T × T', λ (oldListL, oldListR) (oldElementL, oldElementR) (newListL, newListR) =>
                       oldListL = oldElementL :: newListL ∧
                       oldListR = oldElementR :: newListR ⟩)].toAssocList
  }

@[drunfold] def split T T' : NatModule (List T × List T') :=
  { inputs := [ (0, ⟨ T × T', λ (oldListL, oldListR) (newElementL, newElementR) (newListL, newListR) =>
                       newListL = oldListL.concat newElementL ∧ newListR = oldListR.concat newElementR⟩)].toAssocList,
    outputs := [(0, ⟨ T, λ (oldListL, oldListR) oldElementL (newListL, newListR) =>
                       oldListL = oldElementL :: newListL ∧ oldListR = oldListR ⟩),
                (1, ⟨ T', λ (oldListL, oldListR) oldElementR (newListL, newListR) =>
                       oldListR = oldElementR :: newListR ∧ oldListL = oldListL ⟩)].toAssocList
  }

@[drunfold] def branch T : NatModule (List T × List Bool) :=
  { inputs := [ (0, ⟨ T, λ (oldValList, oldBoolList) val (newValList, newBoolList) =>
                           newValList = oldValList.concat val ∧ newBoolList = oldBoolList ⟩)
              , (1, ⟨ Bool, λ (oldValList, oldBoolList) b (newValList, newBoolList) =>
                           newValList = oldValList ∧ newBoolList = oldBoolList.concat b ⟩)
              ].toAssocList
    outputs := [ (0, ⟨ T, λ (oldValList, oldBoolList) val (newValList, newBoolList) =>
                            val :: newValList = oldValList ∧ true :: newBoolList = oldBoolList ⟩)
               , (1, ⟨ T, λ (oldValList, oldBoolList) val (newValList, newBoolList) =>
                            val :: newValList = oldValList ∧ false :: newBoolList = oldBoolList ⟩)
               ].toAssocList
  }

@[drunfold] def mux T : NatModule (List T × List T × List Bool) :=
  { inputs := [ (1, ⟨ T, λ (oldTrueList, oldFalseList, oldBoolList) val (newTrueList, newFalseList, newBoolList) =>
                           newTrueList = oldTrueList.concat val ∧ newFalseList = oldFalseList ∧ newBoolList = oldBoolList ⟩)
              , (2, ⟨ T, λ (oldTrueList, oldFalseList, oldBoolList) val (newTrueList, newFalseList, newBoolList) =>
                           newTrueList = oldTrueList ∧ newFalseList = oldFalseList.concat val ∧ newBoolList = oldBoolList ⟩)
              , (0, ⟨ Bool, λ (oldTrueList, oldFalseList, oldBoolList) b (newTrueList, newFalseList, newBoolList) =>
                           newTrueList = oldTrueList ∧ newFalseList = oldFalseList ∧ newBoolList = oldBoolList.concat b ⟩)
              ].toAssocList
    outputs := [ (0, ⟨ T, λ (oldTrueList, oldFalseList, oldBoolList) val (newTrueList, newFalseList, newBoolList) =>
                            ∃ b, b :: newBoolList = oldBoolList
                              ∧ if b then val :: newTrueList = oldTrueList ∧ newFalseList = oldFalseList
                                     else newTrueList = oldTrueList ∧ val :: newFalseList = oldFalseList ⟩)
               ].toAssocList
  }

@[drunfold] def muxC T : NatModule (List T × List T × List Bool) :=
  { inputs := [ (1, ⟨ T, λ (oldTrueList, oldFalseList, oldBoolList) val (newTrueList, newFalseList, newBoolList) =>
                           newTrueList = oldTrueList.concat val ∧ newFalseList = oldFalseList ∧ newBoolList = oldBoolList ⟩)
              , (2, ⟨ T, λ (oldTrueList, oldFalseList, oldBoolList) val (newTrueList, newFalseList, newBoolList) =>
                           newTrueList = oldTrueList ∧ newFalseList = oldFalseList.concat val ∧ newBoolList = oldBoolList ⟩)
              , (0, ⟨ Bool, λ (oldTrueList, oldFalseList, oldBoolList) b (newTrueList, newFalseList, newBoolList) =>
                           newTrueList = oldTrueList ∧ newFalseList = oldFalseList ∧ newBoolList = oldBoolList.concat b ⟩)
              ].toAssocList
    outputs := [ (0, ⟨ T×Bool, λ (oldTrueList, oldFalseList, oldBoolList) (val, b) (newTrueList, newFalseList, newBoolList) =>
                            b :: newBoolList = oldBoolList
                              ∧ if b then val :: newTrueList = oldTrueList ∧ newFalseList = oldFalseList
                                     else newTrueList = oldTrueList ∧ val :: newFalseList = oldFalseList ⟩)
               ].toAssocList
  }


@[drunfold] def joinC T T' T'' : NatModule (List T × List (T'× T'')) :=
  { inputs := [ (0, ⟨ T, λ (oldListL, oldListR) newElement (newListL, newListR) =>
                       newListL = oldListL.concat newElement ∧ newListR = oldListR⟩)
              , (1, ⟨ T' × T'', λ (oldListL, oldListR) newElement (newListL, newListR) =>
                       newListR = oldListR.concat newElement ∧ newListL = oldListL⟩)].toAssocList,
    outputs := [(0, ⟨ T × T', λ (oldListL, oldListR) (oldElementL, oldElementR) (newListL, newListR) =>
                       ∃ x, oldListL =  oldElementL :: newListL ∧
                       oldListR = (oldElementR, x) :: newListR ⟩)].toAssocList
  }
@[drunfold] def bag T : NatModule (List T) :=
  { inputs := [(0,⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩)].toAssocList,
    outputs := [(0,⟨ T, λ oldList oldElement newList => ∃ i, newList = oldList.remove i ∧ oldElement = oldList.get i ⟩)].toAssocList,
  }

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
        ].toAssocList
  }

/--
Essentially tagger + join without internal rule
-/
@[drunfold] def tagger_untagger_val (TagT : Type 0) [_i: DecidableEq TagT] (T T' : Type 0) : NatModule (List TagT × AssocList TagT T' × List T) :=
  { inputs := [
        -- Complete computation
        -- Models the input of the Cal + Untagger (coming from a previously tagged region)
        (0, ⟨ TagT × T', λ (oldOrder, oldMap, oldVal) (tag,el) (newOrder, newMap, newVal) =>
          -- Tag must be used, but no value ready, otherwise block:
          (tag ∈ oldOrder ∧ oldMap.find? tag = none) ∧
          newMap = oldMap.cons tag el ∧ newOrder = oldOrder ∧ newVal = oldVal ⟩),
        -- Enq a value to be tagged
        -- Models the input of the Tagger (coming from outside)
        (1, ⟨ T, λ (oldOrder, oldMap, oldVal) v (newOrder, newMap, newVal) =>
          newMap = oldMap ∧ newOrder = oldOrder ∧ newVal = oldVal.concat v ⟩)
      ].toAssocList,
    outputs := [
        -- Allocate fresh tag and output with value
        -- Models the output of the Tagger
      (0, ⟨ TagT × T, λ (oldOrder, oldMap, oldVal) (tag, v) (newOrder, newMap, newVal) =>
        -- Tag must be unused otherwise block (alternatively we
        -- could an implication to say undefined behavior):
        (tag ∉ oldOrder ∧ oldMap.find? tag = none) ∧
        newMap = oldMap ∧ newOrder = oldOrder.concat tag ∧ v :: newVal = oldVal⟩),
        -- Dequeue + free tag
        -- Models the output of the Cal + Untagger
      (1, ⟨ T', λ (oldorder, oldmap, oldVal) el (neworder, newmap, newVal) =>
        -- tag must be used otherwise, but no value brought, undefined behavior:
        ∃ tag , oldorder = tag :: neworder ∧ oldmap.find? tag = some el ∧
        newmap = oldmap.eraseAll tag ∧ newVal = oldVal ⟩),
        ].toAssocList
  }

@[drunfold] def tagger (TagT : Type) [DecidableEq TagT] T : NatModule (List (TagT × T) × List TagT) :=
  { inputs := [
        -- Allocate tag
        (0, ⟨ T, λ (oldEl, oldOrder) el (newEl, newOrder) =>
          ∃ tag, tag ∉ oldOrder ∧ newEl = oldEl.concat (tag, el) ∧ newOrder = oldOrder.concat tag ⟩),
        -- Free tag
        (1, ⟨ TagT, λ (oldEl, oldOrder) t (newEl, newOrder) =>
          newOrder = oldOrder.erase t ∧ newEl = oldEl ⟩)
      ].toAssocList,
    outputs := [
        (0, ⟨ TagT × T, λ (oldEl, oldOrder) el (newEl, newOrder) =>
          el :: newEl = oldEl ∧ newOrder = oldOrder⟩)
      ].toAssocList
  }

@[drunfold] def aligner TagT [DecidableEq TagT] T : NatModule (List (TagT × T) × List (TagT × T)) :=
  { inputs := [
        (0, ⟨ TagT × T, λ (oldListL, oldListR) newElement (newListL, newListR) =>
            newListL = oldListL.concat newElement ⟩),
        (1, ⟨ TagT × T, λ (oldListL, oldListR) newElement (newListL, newListR) =>
            newListR = oldListR.concat newElement ⟩)
      ].toAssocList,
    outputs := [
        (0, ⟨ (TagT × T) × (TagT × T), λ (oldListL, oldListR) oldElement (newListL, newListR) =>
           ∃ t v v', (t, v) ∈ oldListL ∧ (t, v') ∈ oldListR
             ∧ newListL = oldListL.eraseP (·.fst = t)
             ∧ newListR = oldListR.eraseP (·.fst = t)
             ∧ oldElement = ((t, v), (t, v')) ⟩)
      ].toAssocList
  }

@[drunfold] def sink (T : Type _) : NatModule Unit :=
  { inputs := [(0, ⟨ T, λ _ _ _ => True ⟩)].toAssocList,
    outputs := ∅
  }

@[drunfold] def unary_op {α R} (f : α → R): NatModule (List α) :=
  { inputs := [
        (0, ⟨ α, λ oldList newElement newList => newList = oldList.concat newElement ⟩)
      ].toAssocList,
    outputs := [
        (0, ⟨ R, λ oldList oldElement newList => ∃ a, a :: newList = oldList ∧ oldElement = f a ⟩)
      ].toAssocList
  }

@[drunfold] def binary_op {α β R} (f : α → β → R): NatModule (List α × List β) :=
  { inputs := [
        (0, ⟨ α, λ (oldListL, oldListR) newElement (newListL, newListR) => newListL = oldListL.concat newElement ⟩),
        (1, ⟨ β, λ (oldListL, oldListR) newElement (newListL, newListR) => newListR = oldListR.concat newElement ⟩)
      ].toAssocList,
    outputs := [
        (0, ⟨ R, λ (oldListL, oldListR) oldElement (newListL, newListR) =>
          ∃ a b, a :: newListL = oldListL
            ∧ b :: newListR = oldListR
            ∧ oldElement = f a b ⟩)
      ].toAssocList
  }

@[drunfold] def constant {T} (t : T) : NatModule (List Unit) :=
  { inputs := [
        (0, ⟨ Unit, λ oldList newElement newList => newList = oldList.concat newElement ⟩)
      ].toAssocList,
    outputs := [
        (0, ⟨ T, λ oldList oldElement newList => ∃ a, a :: newList = oldList ∧ oldElement = t ⟩)
      ].toAssocList
  }

@[drunfold] def sync {T S} : NatModule (List S × List T) :=
  { inputs := [
        (0, ⟨ S, λ (lo, ro) s (ln, rn) => lo.concat s = ln ∧ ro = rn ⟩),
        (1, ⟨ T, λ (lo, ro) t (ln, rn) => ro.concat t = rn ∧ lo = ln ⟩)
      ].toAssocList,
    outputs := [
        (0, ⟨ T, λ (lo, ro) t (ln, rn) => ∃ s, lo = s :: ln ∧ ro = t :: rn ⟩)
      ].toAssocList
  }

@[drunfold] def sync1 {T S} : NatModule (Option S × List T) :=
  { inputs := [
        (0, ⟨ S, λ (lo, ro) s (ln, rn) => lo = none ∧ ln = some s ∧ ro = rn ⟩),
        (1, ⟨ T, λ (lo, ro) t (ln, rn) => ro.concat t = rn ∧ lo = ln ⟩)
      ].toAssocList,
    outputs := [
        (0, ⟨ T, λ (lo, ro) t (ln, rn) => ∃ s, lo = some s ∧ ln = none ∧ ro = t :: rn ⟩)
      ].toAssocList
  }

@[drunfold] def dsync {T S} (f : T → S) : NatModule (List S × List T) :=
  { inputs := [
        (0, ⟨ T, λ (lo, ro) t (ln, rn) => lo.concat (f t) = ln ∧ ro.concat t = rn ⟩),
      ].toAssocList,
    outputs := [
        (0, ⟨ S, λ (lo, ro) s (ln, rn) => lo = s :: ln ⟩),
        (1, ⟨ T, λ (lo, ro) t (ln, rn) => ro = t :: rn ⟩)
      ].toAssocList
  }

@[drunfold] def dsyncU {T} : NatModule (List Unit × List T) := dsync (λ _ => ())

@[drunfold] def dsync1 {T S} (f : T → S) : NatModule (Option S × List T) :=
  { inputs := [
        (0, ⟨ T, λ (lo, ro) t (ln, rn) => lo = none ∧ ln = some (f t) ∧ ro.concat t = rn ⟩),
      ].toAssocList,
    outputs := [
        (0, ⟨ S, λ (lo, ro) s (ln, rn) => lo = some s ∧ ln = none ⟩),
        (1, ⟨ T, λ (lo, ro) t (ln, rn) => ro = t :: rn ⟩)
      ].toAssocList
  }

@[drunfold] def dsync1U {T} : NatModule (Option Unit × List T) := dsync1 (λ _ => ())

@[drunfold] def pure {S T} (f : S → T) : NatModule (List T) :=
  { inputs := [
      (0, ⟨S, λ before el after => after = before.concat (f el)⟩)
    ].toAssocList,
    outputs := [
      (0, ⟨T, λ before el after => el :: after = before⟩)
    ].toAssocList
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
                         ∧ oldListR.val = newListR.val.concat oldElementR ⟩)].toAssocList
  }

@[drunfold] def joinL T T' T'' n : NatModule (BoundedList (T × T') n × BoundedList T'' n) :=
  { inputs := [ (0, ⟨ T × T', λ (oldListL, oldListR) newElement (newListL, newListR) =>
                      newListL.val = newElement :: oldListL.val ∧ newListR = oldListR ⟩)
              , (1, ⟨ T'', λ (oldListL, oldListR) newElement (newListL, newListR) =>
                      newListR.val = newElement :: oldListR.val ∧ newListL = oldListL⟩)].toAssocList,
    outputs := [(0, ⟨ T × T' × T'', λ (oldListL, oldListR)  (oldElementL₁, oldElementL₂, oldElementR) (newListL, newListR) =>
                        oldListL.val = newListL.val.concat (oldElementL₁, oldElementL₂)
                         ∧ oldListR.val = newListR.val.concat oldElementR⟩)].toAssocList
  }

end FixedSize

end DataflowRewriter.NatModule

namespace DataflowRewriter.StringModule

@[drunfold] def bag T : StringModule (List T) := NatModule.bag T
  |>.stringify
  -- |>.mapIdent (λ x => "enq") (λ x => "deq")

@[drunfold] def merge T n := NatModule.merge T n |>.stringify

@[drunfold] def fork T n := NatModule.fork T n |>.stringify

@[drunfold] def forkN T n := NatModule.forkN T n |>.stringify

@[drunfold] def cntrl_merge T := NatModule.cntrl_merge T |>.stringify

@[drunfold] def queue T : StringModule (List T) := NatModule.queue T
  |>.stringify
  -- |>.mapIdent (λ x => "enq") (λ x => "deq")

@[drunfold] def fork2 T := NatModule.fork2 T|>.stringify

@[drunfold] def join T T' := NatModule.join T T' |>.stringify

@[drunfold] def split T T' := NatModule.split T T' |>.stringify

@[drunfold] def sink T := NatModule.sink T |>.stringify

@[drunfold] def branch T := NatModule.branch T
  |>.stringify
  -- |>.mapIdent (λ | 0 => "val" | _ => "cond") (λ | 0 => "true" | _ => "false")

@[drunfold] def mux T := NatModule.mux T
  |>.stringify

@[drunfold] def tagger TagT [DecidableEq TagT] T := NatModule.tagger TagT T
  |>.stringify

@[drunfold] def aligner TagT [DecidableEq TagT] T := NatModule.aligner TagT T
  |>.stringify

@[drunfold] def unary_op {α R} (f : α → R) := NatModule.unary_op f
  |>.stringify

@[drunfold] def binary_op {α β R} (f : α → β → R) := NatModule.binary_op f
  |>.stringify

@[drunfold] def init T default := NatModule.init T default |>.stringify

@[drunfold] def constant {T} (t : T) := NatModule.constant t |>.stringify

@[drunfold] def sync {T S} := @NatModule.sync T S |>.stringify

@[drunfold] def sync1 {T S} := @NatModule.sync1 T S |>.stringify

@[drunfold] def dsync {T S} f := @NatModule.dsync T S f |>.stringify

@[drunfold] def dsyncU {T} := @NatModule.dsyncU T |>.stringify

@[drunfold] def dsync1 {T S} f := @NatModule.dsync1 T S f |>.stringify

@[drunfold] def dsync1U {T} := @NatModule.dsync1U T |>.stringify

@[drunfold] def pure {S T} f := @NatModule.pure S T f |>.stringify

opaque polymorphic_add {T} [Inhabited T] : T → T → T
opaque polymorphic_sub {T} [Inhabited T] : T → T → T
opaque polymorphic_mult {T} [Inhabited T] : T → T → T
opaque polymorphic_div {T} [Inhabited T] : T → T → T
opaque polymorphic_shift_left {T} [Inhabited T] : T → T → T

#reduce (types := true) Lean.MetaM Unit

opaque constant_a {T} [Inhabited T] : T
opaque constant_b {T} [Inhabited T] : T
opaque constant_c {T} [Inhabited T] : T
opaque constant_d {T} [Inhabited T] : T
opaque constant_e {T} [Inhabited T] : T
opaque constant_f {T} [Inhabited T] : T
opaque constant_g {T} [Inhabited T] : T

@[drunfold] def tagger_untagger_val TagT [DecidableEq TagT] T T' :=
  NatModule.tagger_untagger_val TagT T T' |>.stringify

-- Associate the above modules with a String name to be used in the matcher of each rewrite
-- Essentially, those constitute our primitives
def ε (Tag : Type) [DecidableEq Tag] (T : Type) [Inhabited T] : IdentMap String (TModule String) :=
  [ ("Join", ⟨_, StringModule.join T T⟩)
  , ("TaggedJoin", ⟨_, StringModule.join Tag T⟩)

  , ("Split", ⟨_, StringModule.split T T⟩)
  , ("TaggedSplit", ⟨_, StringModule.split Tag T⟩)

  , ("Merge", ⟨_, StringModule.merge T 2⟩)
  , ("TaggedMerge", ⟨_, StringModule.merge (Tag × T) 2⟩)

  , ("Sink", ⟨_, StringModule.sink T⟩)
  , ("TaggedSink", ⟨_, StringModule.sink Tag⟩)

  , ("Fork", ⟨_, StringModule.fork T 2⟩)
  , ("Fork3", ⟨_, StringModule.fork T 3⟩)
  , ("Fork4", ⟨_, StringModule.fork T 4⟩)
  , ("Fork5", ⟨_, StringModule.fork T 5⟩)
  , ("Fork6", ⟨_, StringModule.fork T 6⟩)
  , ("TagggedFork", ⟨_, StringModule.fork (Tag × T) 2⟩)

  , ("CntrlMerge", ⟨_, StringModule.cntrl_merge T⟩)
  , ("TagggedCntrlMerge", ⟨_, StringModule.cntrl_merge (Tag × T)⟩)

  , ("Branch", ⟨_, StringModule.branch T⟩)
  , ("BranchC", ⟨_, StringModule.branch Unit⟩)
  , ("TaggedBranch", ⟨_, StringModule.branch (Tag × T)⟩)

  , ("Mux", ⟨_, StringModule.mux T⟩)
  , ("MuxC", ⟨_, StringModule.mux Unit⟩)
  , ("TagggedMux", ⟨_, StringModule.mux (Tag × T)⟩)

  , ("Buffer", ⟨_, StringModule.queue T⟩)
  , ("BufferC", ⟨_, StringModule.queue Unit⟩)
  , ("BufferB", ⟨_, StringModule.queue Bool⟩)
  , ("TagggedBuffer", ⟨_, StringModule.queue (Tag × T)⟩)

  , ("Bag", ⟨_, StringModule.bag (Tag × T)⟩)

  , ("Aligner", ⟨_, StringModule.aligner Tag T⟩)
  , ("TaggerCntrlAligner", ⟨_, StringModule.tagger_untagger_val Tag T T⟩)

  , ("ConstantA", ⟨_, StringModule.constant (@constant_a T)⟩)
  , ("ConstantB", ⟨_, StringModule.constant (@constant_b T)⟩)
  , ("ConstantC", ⟨_, StringModule.constant (@constant_c T)⟩)
  , ("ConstantD", ⟨_, StringModule.constant (@constant_d T)⟩)
  , ("ConstantE", ⟨_, StringModule.constant (@constant_e T)⟩)
  , ("ConstantF", ⟨_, StringModule.constant (@constant_f T)⟩)
  , ("ConstantG", ⟨_, StringModule.constant (@constant_g T)⟩)

  , ("Add", ⟨_, StringModule.binary_op (@polymorphic_add T _)⟩)
  , ("Mul", ⟨_, StringModule.binary_op (@polymorphic_mult T _)⟩)
  , ("Div", ⟨_, StringModule.binary_op (@polymorphic_div T _)⟩)
  , ("Shl", ⟨_, StringModule.binary_op (@polymorphic_shift_left T _)⟩)
  , ("Sub", ⟨_, StringModule.binary_op (@polymorphic_sub T _)⟩)
  ].toAssocList

@[drunfold] def muxC T := NatModule.muxC T
  |>.stringify

@[drunfold] def joinC T T' T'' := NatModule.joinC T T' T'' |>.stringify

namespace FixedSize

@[drunfold] def join T T' n := NatModule.FixedSize.join T T' n |>.stringify

@[drunfold] def joinL T T' T'' n := NatModule.FixedSize.joinL T T' T'' n |>.stringify

end FixedSize
end DataflowRewriter.StringModule
