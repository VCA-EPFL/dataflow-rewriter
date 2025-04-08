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

variable [T: NocParam]

-- Components ------------------------------------------------------------------

@[drunfold]
def nbranch' (name := "nbranch") : NatModule (NatModule.Named name (List T.Data × List RouterID)) :=
  {
    inputs := [
      (0, ⟨T.Data,
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
      List.range T.netsz |>.map (λ routerID => Prod.mk ↑routerID
        (⟨T.Data,
          λ (oldDatas, oldRouterIDs) data (newDatas, newRouterIDs) =>
            data :: newDatas = oldDatas ∧
            routerID :: newRouterIDs = oldRouterIDs
        ⟩))
      |>.toAssocList,
  }

@[drunfold]
def nbranch :=
  nbranch' |>.stringify

-- Environment -----------------------------------------------------------------

def ε' : Env :=
  [
    -- Merge to implement the n-bag
    (s!"Merge {T.DataS} {T.netsz}", ⟨_, StringModule.merge T.Data T.netsz⟩),

    -- Splits to separate Data and FlitHeader
    (s!"Split {T.DataS} {FlitHeaderS}", ⟨_, StringModule.split T.Data FlitHeader⟩),

    -- Bags to receive message (One per router)
    (s!"Bag {T.DataS}", ⟨_, StringModule.bag T.Data⟩),

    -- Branching for routing
    (s!"NBranch {T.DataS} {T.netsz}", ⟨_, nbranch⟩),
  ].toAssocList

def ε'_merge :
  ε'.find? s!"Merge {T.DataS} {T.netsz}" = .some ⟨_, StringModule.merge T.Data T.netsz⟩ := by
  simpa

def ε'_split :
  ε'.find? s!"Split {T.DataS} {FlitHeaderS}" = .some ⟨_, StringModule.split T.Data FlitHeader⟩ := by
    simp
    -- TODO(Yann): Why cannot I use existential here ?
    exists s!"Split {T.DataS} {FlitHeaderS}"
    right
    split_ands
    · unfold toString instToStringString instToStringNat; simp
      sorry -- Should be Trivial
    · rfl

def ε'_bag :
  ε'.find? s!"Bag {T.DataS}" = .some ⟨_, StringModule.bag T.Data⟩ := by
    simp
    exists s!"Bag {T.DataS}"
    right
    split_ands
    · sorry
    · right
      simp
      sorry

def ε'_nbranch :
  ε'.find? s!"NBranch {T.DataS} {T.netsz}" = .some ⟨_, nbranch⟩ := by
    simp
    exists s!"NBranch {T.DataS} {T.netsz}"
    right
    split_ands
    · sorry
    · right; simp; split_ands
      · sorry
      · right
        sorry
