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
import DataflowRewriter.Component
import DataflowRewriter.KernelRefl
import DataflowRewriter.Reduce
import DataflowRewriter.List
import DataflowRewriter.Tactic
import DataflowRewriter.AssocList
import DataflowRewriter.Examples.NoC.Basic

open Batteries (AssocList)

namespace DataflowRewriter.NoC

variable [P: NocParam]

-- Components ------------------------------------------------------------------
-- Reference semantics for useful components
-- Implementation is provided in `ExprLow` and `ExprHigh` using base components

@[drunfold]
def nbranch' (name := "nbranch") : NatModule (NatModule.Named name (List P.Data × List RouterID)) :=
  {
    inputs := [
      (0, ⟨P.Data,
        λ (oldDatas, oldRouterIDs) data (newDatas, newRouterIDs) =>
          newDatas = oldDatas.concat data ∧ newRouterIDs = oldRouterIDs
      ⟩),
      (1, ⟨RouterID,
        λ (oldDatas, oldRouterIDs) routerID (newDatas, newRouterIDs) =>
          newDatas = oldDatas ∧ newRouterIDs = oldRouterIDs.concat routerID
      ⟩),
    ].toAssocList

    outputs :=
      -- TODO: We would like to have n be cast to a RouterID down the line
      List.range P.netsz |>.map (λ routerID => Prod.mk ↑routerID
        (⟨P.Data,
          λ (oldDatas, oldRouterIDs) data (newDatas, newRouterIDs) =>
            data :: newDatas = oldDatas ∧
            routerID :: newRouterIDs = oldRouterIDs
        ⟩))
      |>.toAssocList,
  }

@[drunfold]
def nbranch :=
  nbranch' |>.stringify

def mk_nbag_input_rule (S : Type) (_ : Nat) : (Σ T : Type, List S → T → List S → Prop) :=
    ⟨ S, λ oldState v newState => newState = oldState.concat v ⟩

-- Bag with `n` inputs
@[drunfold]
def nbag' (T : Type) (n : Nat) (name := "nbag") : NatModule (NatModule.Named name (List T)) :=
  {
    inputs := List.range n |>.map (lift_f (mk_nbag_input_rule T)) |>.toAssocList,
    outputs := [(↑0, ⟨ T, λ oldState v newState => ∃ i, newState = oldState.remove i ∧ v = oldState.get i ⟩)].toAssocList,
  }

@[drunfold]
def nbag T n :=
  nbag' T n |>.stringify

-- Final Environment -----------------------------------------------------------

def ε' : Env :=
  [
    -- Merge to implement the n-bag
    (s!"Merge {P.DataS} {P.netsz}", ⟨_, StringModule.merge P.Data P.netsz⟩),

    -- Splits to separate Data and FlitHeader
    (s!"Split {P.DataS} {FlitHeaderS}", ⟨_, StringModule.split P.Data FlitHeader⟩),

    -- Bags to receive message (One per router)
    (s!"Bag {P.DataS}", ⟨_, StringModule.bag P.Data⟩),

    -- Branching for routing
    (s!"NBranch {P.DataS} {P.netsz}", ⟨_, nbranch⟩),
  ].toAssocList

-- All of the following Lemmas are used for precomputing modules
-- TODO: We should probably make the proof into a tactic

def ε'_merge :
  ε'.find? s!"Merge {P.DataS} {P.netsz}" = .some ⟨_, StringModule.merge P.Data P.netsz⟩ := by
  simpa

def ε'_split :
  ε'.find? s!"Split {P.DataS} {FlitHeaderS}" = .some ⟨_, StringModule.split P.Data FlitHeader⟩ := by
    simp
    -- TODO(Ask Yann): Why cannot I use existential here ?
    exists s!"Split {P.DataS} {FlitHeaderS}"
    right
    split_ands
    · unfold toString instToStringString instToStringNat; simp
      sorry -- Should be Trivial
    · rfl

def ε'_bag :
  ε'.find? s!"Bag {P.DataS}" = .some ⟨_, StringModule.bag P.Data⟩ := by
    simp
    exists s!"Bag {P.DataS}"
    right
    split_ands
    · sorry -- Should be Trivial
    · right
      simp
      sorry

def ε'_nbranch :
  ε'.find? s!"NBranch {P.DataS} {P.netsz}" = .some ⟨_, nbranch⟩ := by
    simp
    exists s!"NBranch {P.DataS} {P.netsz}"
    right
    split_ands
    · sorry -- Should be Trivial
    · right; simp; split_ands
      · sorry -- Should be Trivial
      · right
        sorry -- Should be Trivial
