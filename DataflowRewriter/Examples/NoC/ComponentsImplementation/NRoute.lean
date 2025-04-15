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
import DataflowRewriter.Examples.NoC.BasicLemmas
import DataflowRewriter.Examples.NoC.Components

open Batteries (AssocList)

namespace DataflowRewriter.NoC

variable [P: NocParam]

attribute [drcompute] Batteries.AssocList.toList Function.uncurry Module.mapIdent
  List.toAssocList List.foldl Option.pure_def Option.bind_eq_bind Option.bind_some
  Module.renamePorts Batteries.AssocList.mapKey InternalPort.map Nat.repr
  Nat.toDigits Nat.toDigitsCore Nat.digitChar List.asString Option.bind
  Batteries.AssocList.mapVal beq_self_eq_true
  Option.getD cond beq_self_eq_true beq_iff_eq  InternalPort.mk.injEq
  String.reduceEq and_false imp_self BEq.beq AssocList.bijectivePortRenaming
  AssocList.keysList List.inter AssocList.filterId
  AssocList.append AssocList.filter

attribute [drdecide] InternalPort.mk.injEq and_false decide_False decide_True
  and_true Batteries.AssocList.eraseAllP  InternalPort.mk.injEq
  and_false decide_False decide_True reduceCtorEq cond List.map List.elem_eq_mem
  List.mem_cons List.mem_singleton Bool.decide_or InternalPort.mk.injEq
  String.reduceEq and_false decide_false reduceCtorEq and_self Bool.or_self
  Bool.false_eq_true not_false_eq_true List.filter_cons_of_neg and_true
  List.filter_nil List.empty_eq decide_true List.nodup_cons List.not_mem_nil
  List.nodup_nil Bool.and_self reduceIte List.concat_eq_append dreduceIte
  List.append_nil

-- Implementation --------------------------------------------------------------

def ε_nroute : Env :=
  [
    (s!"Split {P.DataS} {FlitHeaderS}", ⟨_, StringModule.split P.Data FlitHeader⟩),
    (s!"NBranch {P.DataS} {P.netsz}", ⟨_, StringModule.bag P.Data⟩),
  ].toAssocList

def ε_nroute_split :
  ε_nroute.find? s!"Split {P.DataS} {FlitHeaderS}" = .some ⟨_, StringModule.split P.Data FlitHeader⟩ := by
  simpa

def ε_nroute_nbranch :
  ε_nroute.find? s!"NBranch {P.DataS} {P.netsz}" = .some ⟨_, nroute⟩ := by
    sorry

def nroute_low : ExprLow String :=
  let split := ExprLow.base
    {
      input := [
        ⟨NatModule.stringify_input 0, NatModule.stringify_input 0⟩
      ].toAssocList,
      output := [
        ⟨
          NatModule.stringify_output 0,
          { inst := InstIdent.internal "Split", name := NatModule.stringify_output 0 }
        ⟩,
        ⟨
          NatModule.stringify_output 1,
          { inst := InstIdent.internal "Split", name := NatModule.stringify_output 1 }
        ⟩
      ].toAssocList,
    }
    s!"Split {P.DataS} {FlitHeaderS}"
  let nbranch := ExprLow.base
    {
      input := [
        ⟨
          NatModule.stringify_input 0,
          { inst := InstIdent.internal "NBranch", name := NatModule.stringify_input 0 }
        ⟩,
        ⟨
          NatModule.stringify_input 1,
          { inst := InstIdent.internal "NBranch", name := NatModule.stringify_input 1 }
        ⟩,
      ].toAssocList,
      output := List.range P.netsz |>.map (λ i => ⟨
        NatModule.stringify_output i,
        NatModule.stringify_output i,
      ⟩) |>.toAssocList,
    }
    s!"NBranch {P.DataS} {P.netsz}"
  let connection (i : Nat) : Connection String :=
    {
      output := {
        inst := InstIdent.internal "Split",
        name := NatModule.stringify_output i
      },
      input := {
        inst := InstIdent.internal "NBranch",
        name := NatModule.stringify_input i
      },
    }
  ExprLow.product split nbranch
  |> ExprLow.connect (connection 0)
  |> ExprLow.connect (connection 1)

def nroute_lowT : Type := by
  precomputeTac [T| nroute_low, ε_nroute] by
    simp [drunfold, seval, drdecide, -AssocList.find?_eq]
    rw [ε_nroute_split, ε_nroute_nbranch]
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,-AssocList.mapKey_mapKey]

def nroute_lowM : StringModule nroute_lowT := by
  precomputeTac [e| nroute_low, ε_nroute] by
    simp [drunfold, seval, drdecide, -AssocList.find?_eq]
    rw [ε_nroute_split, ε_nroute_nbranch]
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq]
    conv =>
      pattern (occs := *) Module.connect'' _ _
      all_goals
        rw [(Module.connect''_dep_rw (h := by simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?]; rfl)
                                     (h' := by simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?]; rfl))]; rfl
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?,AssocList.filter,-Prod.exists]
    unfold Module.connect''
    simp
    simp [AssocList.mapKey_mapKey, AssocList.mapVal_mapKey]
    simp [AssocList.mapVal_map_toAssocList]
    simp [AssocList.mapKey_map_toAssocList]
    simp [AssocList.bijectivePortRenaming_same]
    simp [InternalPort.map]
    simp [toString]
    -- TODO:
    -- have Hneq: ∀ x,
    --   ({ inst := InstIdent.top, name := NatModule.stringify_input x }: InternalPort String)
    --   ≠ ({ inst := InstIdent.internal "Bag", name := "merge_to_bag_in" }: InternalPort String)
    -- · simpa
    -- simp [AssocList.eraseAll_map_neq (Hneq := Hneq)]
    -- simp [AssocList.eraseAll]
    -- simp [Module.liftR]

-- Correctness -----------------------------------------------------------------
-- TODO

end DataflowRewriter.NoC
