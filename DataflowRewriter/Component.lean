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

@[drunfold] def cntrl_merge T : NatModule (List T × List Bool) :=
  { inputs := [ (0, ⟨ T, λ (oldListL, oldListR) newElement (newListL, newListR) =>
                    newListL = newElement :: oldListL ∧ newListR = true :: oldListR ⟩)
              , (1, ⟨ T, λ (oldListL, oldListR) newElement (newListL, newListR) =>
                    newListL = newElement :: oldListL ∧ newListR = false :: oldListR ⟩)
              ].toAssocList,
    outputs := [ (0, ⟨ T, λ (oldListL, oldListR) oldElement (newListL, newListR) =>
                    newListL.concat oldElement = oldListL ∧ newListR = oldListR ⟩)
               , (1, ⟨ Bool, λ (oldListL, oldListR) oldElement (newListL, newListR) =>
                    newListR.concat oldElement = oldListR ∧ newListL = oldListL ⟩)
               ].toAssocList,
    internals := []
  }

@[drunfold] def cntrl_merge_n T (n : Nat) : NatModule (List T × List Nat) :=
  { inputs := List.range n |>.map (Prod.mk ↑· (⟨ T, λ (oldListL, oldListR) newElement (newListL, newListR) =>
                newListL = newElement :: oldListL ∧ newListR = n :: oldListR ⟩)) |>.toAssocList,
    outputs := [ (0, ⟨ T, λ (oldListL, oldListR) oldElement (newListL, newListR) =>
                       newListL.concat oldElement = oldListL ∧ newListR = oldListR ⟩)
               , (1, ⟨ Nat, λ (oldListL, oldListR) oldElement (newListL, newListR) =>
                       newListR.concat oldElement = oldListR ∧ newListL = oldListL ⟩)
               ].toAssocList,
    internals := []
  }

@[drunfold] def fork T (n : Nat) : NatModule (List T) :=
  { inputs := [(0, ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩)].toAssocList,
    outputs := List.range n |>.map (Prod.mk ↑· ⟨ T, λ oldList oldElement newList => ∃ i, newList = oldList.remove i ∧ oldElement = oldList.get i ⟩) |>.toAssocList,
    internals := []
  }

@[drunfold] def queue T : NatModule (List T) :=
  { inputs := [(⟨ .top, 0 ⟩, ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩)].toAssocList,
    outputs := [(⟨ .top, 0 ⟩, ⟨ T, λ oldList oldElement newList =>  newList.concat oldElement = oldList ⟩)].toAssocList,
    internals := []
  }

@[drunfold] def join T T' : NatModule (List T × List T') :=
  { inputs := [ (0, ⟨ T, λ (oldListL, oldListR) newElement (newListL, newListR) =>
                       newListL = newElement :: oldListL ∧ newListR = oldListR⟩)
              , (1, ⟨ T', λ (oldListL, oldListR) newElement (newListL, newListR) =>
                       newListR = newElement :: oldListR ∧ newListL = oldListL⟩)].toAssocList,
    outputs := [(0, ⟨ T × T', λ (oldListL, oldListR) (oldElementL, oldElementR) (newListL, newListR) =>
                       oldListL = newListL.concat oldElementL ∧
                       oldListR = newListR.concat oldElementR ⟩)].toAssocList,
    internals := []
  }

@[drunfold] def split T T' : NatModule (List T × List T') :=
  { inputs := [ (0, ⟨ T × T', λ (oldListL, oldListR) (newElementL, newElementR) (newListL, newListR) =>
                       newListL = newElementL :: oldListL ∧ newListR = newElementR :: oldListR⟩)].toAssocList,
    outputs := [(0, ⟨ T, λ (oldListL, oldListR) oldElementL (newListL, newListR) =>
                       oldListL = newListL.concat oldElementL ∧ oldListR = oldListR ⟩),
                (1, ⟨ T', λ (oldListL, oldListR) oldElementR (newListL, newListR) =>
                       oldListR = newListR.concat oldElementR ∧ oldListL = oldListL ⟩)].toAssocList,
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
                           newTrueList = val :: oldTrueList ∧ newFalseList = oldFalseList ∧ newBoolList = oldBoolList ⟩)
              , (1, ⟨ T, λ (oldTrueList, oldFalseList, oldBoolList) val (newTrueList, newFalseList, newBoolList) =>
                           newTrueList = oldTrueList ∧ newFalseList = val :: oldFalseList ∧ newBoolList = oldBoolList ⟩)
              , (2, ⟨ Bool, λ (oldTrueList, oldFalseList, oldBoolList) b (newTrueList, newFalseList, newBoolList) =>
                           newTrueList = oldTrueList ∧ newFalseList = oldFalseList ∧ newBoolList = b :: oldBoolList ⟩)
              ].toAssocList
    outputs := [ (0, ⟨ T, λ (oldTrueList, oldFalseList, oldBoolList) val (newTrueList, newFalseList, newBoolList) =>
                            ∃ b, newBoolList.concat b = oldBoolList
                              ∧ if b then newTrueList.concat val = oldTrueList ∧ newFalseList = oldFalseList
                                     else newTrueList = oldTrueList ∧ newFalseList.concat val = oldFalseList ⟩)
               ].toAssocList
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
        (1, ⟨ T, λ (oldOrder, oldMap, oldVal) v (newOrder, newMap, newVal) =>
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
        ∃ tag , oldorder = neworder.concat tag ∧ oldmap.find? tag = some el ∧
        newmap = oldmap.eraseAll tag ∧ newVal = oldVal ⟩),
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

@[drunfold] def aligner TagT [DecidableEq TagT] T : NatModule (List (TagT × T) × List (TagT × T)) :=
  { inputs := [
        (0, ⟨ TagT × T, λ (oldListL, oldListR) newElement (newListL, newListR) =>
            newListL = newElement :: oldListL ⟩),
        (1, ⟨ TagT × T, λ (oldListL, oldListR) newElement (newListL, newListR) =>
            newListR = newElement :: oldListR ⟩)
      ].toAssocList,
    outputs := [
        (0, ⟨ (TagT × T) × (TagT × T), λ (oldListL, oldListR) oldElement (newListL, newListR) =>
           ∃ t v v', (t, v) ∈ oldListL ∧ (t, v') ∈ oldListR
             ∧ newListL = oldListL.eraseP (·.fst = t)
             ∧ newListR = oldListR.eraseP (·.fst = t)
             ∧ oldElement = ((t, v), (t, v')) ⟩)
      ].toAssocList,
    internals := []
  }

@[drunfold] def unary_op {α R} (f : α → R): NatModule (List α) :=
  { inputs := [
        (0, ⟨ α, λ oldList newElement newList => newList = newElement :: oldList ⟩)
      ].toAssocList,
    outputs := [
        (0, ⟨ R, λ oldList oldElement newList => ∃ a, newList.concat a = oldList ∧ oldElement = f a ⟩)
      ].toAssocList,
    internals := []
  }

@[drunfold] def binary_op {α β R} (f : α → β → R): NatModule (List α × List β) :=
  { inputs := [
        (0, ⟨ α, λ (oldListL, oldListR) newElement (newListL, newListR) => newListL = newElement :: oldListL ⟩),
        (1, ⟨ β, λ (oldListL, oldListR) newElement (newListL, newListR) => newListR = newElement :: oldListR ⟩)
      ].toAssocList,
    outputs := [
        (0, ⟨ R, λ (oldListL, oldListR) oldElement (newListL, newListR) =>
          ∃ a b, newListL.concat a = oldListL
            ∧ newListR.concat b = oldListR
            ∧ oldElement = f a b ⟩)
      ].toAssocList,
    internals := []
  }

@[drunfold] def constant {T} (t : T) : NatModule (List Unit) :=
  { inputs := [
        (0, ⟨ Unit, λ oldList newElement newList => newList = newElement :: oldList ⟩)
      ].toAssocList,
    outputs := [
        (0, ⟨ T, λ oldList oldElement newList => ∃ a, newList.concat a = oldList ∧ oldElement = t ⟩)
      ].toAssocList,
    internals := []
  }

end DataflowRewriter.NatModule

namespace DataflowRewriter.StringModule

@[drunfold] def bag T : StringModule (List T) := NatModule.bag T
  |>.stringify
  -- |>.mapIdent (λ x => "enq") (λ x => "deq")

@[drunfold] def merge T n := NatModule.merge T n |>.stringify

@[drunfold] def fork T n := NatModule.fork T n |>.stringify

@[drunfold] def cntrl_merge T := NatModule.cntrl_merge T |>.stringify

@[drunfold] def queue T : StringModule (List T) := NatModule.queue T
  |>.stringify
  -- |>.mapIdent (λ x => "enq") (λ x => "deq")

@[drunfold] def join T T' := NatModule.join T T' |>.stringify

@[drunfold] def split T T' := NatModule.split T T' |>.stringify

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

@[drunfold] def constant {T} (t : T) := NatModule.constant t |>.stringify

opaque polymorphic_add {T} [Inhabited T] : T → T → T
opaque polymorphic_sub {T} [Inhabited T] : T → T → T
opaque polymorphic_mult {T} [Inhabited T] : T → T → T
opaque polymorphic_div {T} [Inhabited T] : T → T → T
opaque polymorphic_shift_left {T} [Inhabited T] : T → T → T

opaque constant_a {T} [Inhabited T] : T
opaque constant_b {T} [Inhabited T] : T
opaque constant_c {T} [Inhabited T] : T
opaque constant_d {T} [Inhabited T] : T
opaque constant_e {T} [Inhabited T] : T
opaque constant_f {T} [Inhabited T] : T
opaque constant_g {T} [Inhabited T] : T

@[drunfold] def tagger_untagger_val TagT [DecidableEq TagT] T :=
  NatModule.tagger_untagger_val TagT T |>.stringify

def ε (Tag : Type) [DecidableEq Tag] (T : Type) [Inhabited T] : IdentMap String (TModule String) :=
  [ ("Join", ⟨_, StringModule.join T T⟩)
  , ("TaggedJoin", ⟨_, StringModule.join Tag T⟩)

  , ("Split", ⟨_, StringModule.split T T⟩)
  , ("TaggedSplit", ⟨_, StringModule.split Tag T⟩)

  , ("Merge", ⟨_, StringModule.merge T 2⟩)
  , ("TagggedMerge", ⟨_, StringModule.merge (Tag × T) 2⟩)

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
  , ("TaggerCntrlAligner", ⟨_, StringModule.tagger_untagger_val Tag T⟩)

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

end DataflowRewriter.StringModule
