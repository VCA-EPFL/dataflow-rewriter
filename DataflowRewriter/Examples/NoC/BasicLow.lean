/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import Lean
import Init.Data.BitVec.Lemmas
import Qq

import DataflowRewriter.Simp
import DataflowRewriter.Module
import DataflowRewriter.ExprLow
import DataflowRewriter.ExprLowLemmas
import DataflowRewriter.Component
import DataflowRewriter.KernelRefl
import DataflowRewriter.Reduce
import DataflowRewriter.List
import DataflowRewriter.Tactic
import DataflowRewriter.AssocList
import DataflowRewriter.Examples.NoC.Basic
import DataflowRewriter.Examples.NoC.Components

open Batteries (AssocList)

namespace DataflowRewriter.NoC

variable [P: NocParam]

attribute [drcompute] Batteries.AssocList.toList Function.uncurry Module.mapIdent List.toAssocList List.foldl Option.pure_def Option.bind_eq_bind Option.bind_some Module.renamePorts Batteries.AssocList.mapKey InternalPort.map Nat.repr Nat.toDigits Nat.toDigitsCore Nat.digitChar List.asString Option.bind Batteries.AssocList.mapVal Batteries.AssocList.eraseAll Batteries.AssocList.eraseP beq_self_eq_true Option.getD cond beq_self_eq_true  beq_iff_eq  InternalPort.mk.injEq  String.reduceEq  and_false  imp_self BEq.beq AssocList.bijectivePortRenaming AssocList.keysList AssocList.eraseAllP List.inter AssocList.filterId AssocList.append AssocList.filter

attribute [drdecide] InternalPort.mk.injEq and_false decide_False decide_True and_true Batteries.AssocList.eraseAllP  InternalPort.mk.injEq
  and_false  decide_False  decide_True  reduceCtorEq  cond  List.map List.elem_eq_mem List.mem_cons List.mem_singleton Bool.decide_or InternalPort.mk.injEq
  String.reduceEq and_false decide_false reduceCtorEq and_self Bool.or_self Bool.false_eq_true not_false_eq_true
  List.filter_cons_of_neg and_true List.filter_nil List.empty_eq decide_true List.nodup_cons List.not_mem_nil
  List.nodup_nil Bool.and_self reduceIte List.concat_eq_append dreduceIte List.append_nil

-- Base environment ------------------------------------------------------------

def ε_base : Env :=
  [
    (s!"Merge {P.DataS} {P.netsz}", ⟨_, StringModule.merge P.Data P.netsz⟩),
    (s!"Split {P.DataS} {FlitHeaderS}", ⟨_, StringModule.split P.Data FlitHeader⟩),
    (s!"Bag {P.DataS}", ⟨_, StringModule.bag P.Data⟩),
  ].toAssocList

def ε_base_merge :
  ε_base.find? s!"Merge {P.DataS} {P.netsz}" = .some ⟨_, StringModule.merge P.Data P.netsz⟩ := by
  simpa

def ε_base_split :
  ε_base.find? s!"Split {P.DataS} {FlitHeaderS}" = .some ⟨_, StringModule.split P.Data FlitHeader⟩ := by
    simp
    exists s!"Split {P.DataS} {FlitHeaderS}"
    right
    split_ands
    · unfold toString instToStringString instToStringNat; simp
      sorry -- Should be Trivial
    · rfl

def ε_base_bag :
  ε_base.find? s!"Bag {P.DataS}" = .some ⟨_, StringModule.bag P.Data⟩ := by
    simp
    exists s!"Bag {P.DataS}"
    right
    split_ands
    · sorry -- Should be Trivial
    · right
      simp
      sorry -- Should be Trivial

-- Implementation --------------------------------------------------------------

-- TODO: We should be able to reason about this design inductively but it may be
-- very hard since n is a direct parameter of the merge
-- Another possibility would be to not use a nmerge but only use `two merge`
-- combined in cascade
def nbag_low : ExprLow String :=
  let merge := ExprLow.base
    {
      input := List.range P.netsz |>.map (λ i => ⟨
        -- Type port (Must be inst InstIdent.top)
        NatModule.stringify_input i,
        -- Internal name, here a top level port
        NatModule.stringify_input i,
      ⟩) |>.toAssocList,
      output := [⟨
          -- Type port (Must be inst InstIdent.top)
          NatModule.stringify_output 0,
          -- Internal name
          { inst := InstIdent.internal "Merge", name := "merge_to_bag_out" }
      ⟩].toAssocList,
    }
    s!"Merge {P.DataS} {P.netsz}" -- Instance Type
  let bag := ExprLow.base
    {
      input := [⟨
        NatModule.stringify_input 0,
        { inst := InstIdent.internal "Bag", name := "merge_to_bag_in" }
      ⟩].toAssocList,
      output := [⟨
        NatModule.stringify_output 0,
        NatModule.stringify_output 0
      ⟩].toAssocList,
    }
    s!"Bag {P.DataS}" -- Instance Type
  ExprLow.connect
    {
      output  := { inst := InstIdent.internal "Merge",  name := "merge_to_bag_out"  },
      input   := { inst := InstIdent.internal "Bag",    name := "merge_to_bag_in"   },
    }
    (ExprLow.product bag merge)

def nbag_lowT :=
  [T| nbag_low, ε_base]

def nbag_lowT_precompute : Type := by
  precomputeTac nbag_lowT by
    unfold nbag_lowT
    simp [drunfold, seval, drdecide, -AssocList.find?_eq]
    rw [ε_base_merge, ε_base_bag]
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq]

-- This should be spit out automatically
axiom nbagT_eq : nbag_lowT = nbag_lowT_precompute

def nbag_lowM :=
  [e| nbag_low, ε_base]

def nbagM_precompute : StringModule nbag_lowT_precompute := by
  precomputeTac nbag_lowM by
    unfold nbag_lowM
    simp [drunfold, seval, drdecide, -AssocList.find?_eq]
    rw [ε_base_merge, ε_base_bag]
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq]
    -- rw [AssocList.find?_gss]
    conv =>
      pattern (occs := *) Module.connect'' _ _
      all_goals
        rw [(Module.connect''_dep_rw (h := by simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?]; rfl)
                                     (h' := by simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?]; rfl))]; rfl
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?,AssocList.filter,-Prod.exists]
    unfold Module.connect''
    simp

-- Correctness of nbag implementation ------------------------------------------

variable (T : Type)
variable (TS : String)
variable (n : ℕ)

instance : MatchInterface nbag_lowM (nbag P.Data P.netsz) where
  input_types := by sorry
  output_types := by sorry
  inputs_present := by sorry
  outputs_present := by sorry

end DataflowRewriter.NoC
