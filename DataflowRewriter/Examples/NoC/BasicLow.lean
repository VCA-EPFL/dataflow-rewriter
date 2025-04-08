/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

-- Implementation of NoC types and reference implementation using Bags
-- Inputs are defined as a product between an arbitrary type T and a FlitHeader
-- type, which gives information about the desired target of each message.

-- FIXME: For now, there is a low of useless comments which should be removed

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

open Batteries (AssocList)

namespace DataflowRewriter.NoC

-- Parameters ------------------------------------------------------------------
-- TODO: Use types from Noc/Basic instead

-- TODO: Maybe a comment here to explain Yann's hack would be great since this
-- is also an Example file
class NocParam where
  Data : Type     -- Type of data transmitted over the NoC
  DataS : String  -- String representation of Data
  netsz : Nat     -- Network Size (Number of router)

variable [T: NocParam]

-- Types -----------------------------------------------------------------------
-- TODO: Use types from Noc/Basic instead

def RouterID : Type :=
  -- FIXME: This should be Fin T.netsz, but it is annoying
  -- Notably below for the `nbranch` component, we cannot use a List.range
  Nat

structure FlitHeader : Type :=
  dest : RouterID
-- TODO: Should this be deriving stuff ? I cannot for some reason make it work

def FlitHeaderS : String :=
  s!"FlitHeader {T.netsz}"

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

-- def ε'_merge_fixed n :
--   ε'.find? s!"Merge {T.DataS} {n}" = .some ⟨_, StringModule.merge T.Data n⟩ := by sorry

def ε'_split :
  ε'.find? s!"Split {T.DataS} {FlitHeaderS}" = .some ⟨_, StringModule.split T.Data FlitHeader⟩ := by
    simp
    exists s!"Split {T.DataS} {FlitHeaderS}"
    right
    split_ands
    · sorry
    · rfl

def ε'_bag :
  ε'.find? s!"Bag {T.DataS}" = .some ⟨_, StringModule.bag T.Data⟩ := by
    simp
    sorry

def ε'_nbranch :
  ε'.find? s!"NBranch {T.DataS} {T.netsz}" = .some ⟨_, nbranch⟩ := by
    simp
    sorry

-- Implementation --------------------------------------------------------------

-- Bag with `n` inputs
-- TODO: We should be able to reason about this design inductively but it may be
-- very hard since n is a direct parameter of the merge
-- Another possibility would be to not use a nmerge but only use a two merge,
def nbag (T : Type) (TS : String) (n : ℕ) : ExprLow String :=
  let merge := ExprLow.base
    {
      input := List.range n |>.map (λ i => ⟨
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
    s!"Merge {TS} {n}" -- Instance Type
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
    s!"Bag {TS}" -- Instance Type
  ExprLow.connect
    { inst := InstIdent.internal "Merge", name := "merge_to_bag_out"  }
    { inst := InstIdent.internal "Bag",   name := "merge_to_bag_in"   }
    (ExprLow.product bag merge)

def nbagT :=
  [T| nbag T.Data T.DataS T.netsz, ε']

def nbagM :=
  [e| nbag T.Data T.DataS T.netsz, ε']

def nbagT_precompute : Type := by
  precomputeTac nbagT by
    unfold nbagT
    simp [drunfold,seval,drdecide,-AssocList.find?_eq]
    rw [ε'_merge,ε'_bag]
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq]

-- This should be spit out automatically
axiom nbagT_eq : nbagT = nbagT_precompute

def nbagM_precompute : StringModule nbagT_precompute := by
  precomputeTac nbagM by
    simp [drunfold,seval,drdecide,-AssocList.find?_eq]
    unfold nbagM nbag
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq]
    rw [ε'_merge,ε'_bag]
    dsimp
    -- rw [AssocList.find?_gss]
    conv =>
      pattern (occs := *) Module.connect'' _ _
      all_goals
        rw [(Module.connect''_dep_rw (h := by simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?]; rfl)
                                     (h' := by simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?]; rfl))]; rfl
    -- simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,-Prod.exists]
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?,AssocList.filter,-Prod.exists]
    unfold Module.connect''
    simp

end DataflowRewriter.NoC
