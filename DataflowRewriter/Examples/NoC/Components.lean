/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import Lean
import Init.Data.BitVec.Lemmas
import Qq

import DataflowRewriter.Module
import DataflowRewriter.Component

import DataflowRewriter.Examples.NoC.Basic

namespace DataflowRewriter.NoC

variable [P: NocParam]

-- Utils -----------------------------------------------------------------------

-- TODO: This should be somewhere else, this function is very useful for
-- defining List.range n |>.map (lift_f f) |>.toAssocList, a very common pattern
-- to design parametric design
def lift_f {α : Type} (f : Nat → (Σ T : Type, α → T → α → Prop)) (n : Nat) : InternalPort Nat × (Σ T : Type, α → T → α → Prop) :=
  ⟨↑n, f n⟩

-- Components ------------------------------------------------------------------
-- Reference semantics for useful components
-- Implementation is provided in `ExprLow` and `ExprHigh` using base components

-- Branch with `n` outputs
@[drunfold]
def nbranch' (name := "nbranch") : NatModule (NatModule.Named name (List P.Data × List FlitHeader)) :=
  {
    inputs := [
      (0, ⟨P.Data,
        λ (oldDatas, oldRouterIDs) data (newDatas, newRouterIDs) =>
          newDatas = oldDatas.concat data ∧ newRouterIDs = oldRouterIDs
      ⟩),
      (1, ⟨FlitHeader,
        λ (oldDatas, oldRouterIDs) rID (newDatas, newRouterIDs) =>
          newDatas = oldDatas ∧ newRouterIDs = oldRouterIDs.concat rID
      ⟩),
    ].toAssocList,
    outputs :=
      List.range P.netsz |>.map (λ routerID => Prod.mk ↑routerID
        ⟨P.Data,
          λ (oldDatas, oldRouterIDs) data (newDatas, newRouterIDs) =>
            data :: newDatas = oldDatas ∧
            { dest := routerID } :: newRouterIDs = oldRouterIDs
        ⟩)
      |>.toAssocList,
    init_state := λ s => s = ⟨[], []⟩,
  }

def nrouteT := List (P.Data × FlitHeader)

def mk_nroute_output_rule (rID : RouterID) : (Σ T : Type, nrouteT → T → nrouteT → Prop) :=
  ⟨
    P.Data,
    λ oldState data newState => oldState = (data, { dest := rID }) :: newState
  ⟩

-- NBranch with only one input
@[drunfold]
def nroute' (name := "nroute") : NatModule (NatModule.Named name nrouteT) :=
  {
    inputs := [
      (0, ⟨P.Data × FlitHeader,
        λ oldState v newState => newState = oldState.concat v⟩),
    ].toAssocList,
    outputs := List.range P.netsz |>.map (lift_f mk_nroute_output_rule) |>.toAssocList
    init_state := λ s => s = [],
  }

def mk_nbag_input_rule (S : Type) (_ : Nat) : (Σ T : Type, List S → T → List S → Prop) :=
    ⟨ S, λ oldState v newState => newState = oldState.concat v ⟩

-- Bag with `n` inputs
@[drunfold]
def nbag' (T : Type) (n : Nat) (name := "nbag") : NatModule (NatModule.Named name (List T)) :=
  {
    inputs := List.range n |>.map (lift_f (mk_nbag_input_rule T)) |>.toAssocList,
    outputs := [
      (↑0, ⟨ T, λ oldState v newState =>
        ∃ i, newState = oldState.remove i ∧ v = oldState.get i ⟩)
    ].toAssocList,
    init_state := λ s => s = [],
  }

def nocT : Type :=
  List (P.Data × FlitHeader)

def mk_noc_input_rule (rID : RouterID) : (Σ T : Type, nocT → T → nocT → Prop) :=
    ⟨
      P.Data × FlitHeader,
      λ oldState v newState => newState = v :: oldState
    ⟩

def mk_noc_output_rule (rID : RouterID) : (Σ T : Type, nocT → T → nocT → Prop) :=
    ⟨
      P.Data,
      λ oldState data newState =>
        ∃ i, newState = oldState.remove i ∧
        (data, { dest := rID }) = oldState.get i
    ⟩

-- NOTE: This spec of a NoC also seems to be perfect for the spec of a router?
@[drunfold]
def noc' (name := "noc") : NatModule (NatModule.Named name nocT) :=
  {
    inputs := List.range P.netsz |>.map (lift_f mk_noc_input_rule) |>.toAssocList,
    outputs := List.range P.netsz |>.map (lift_f mk_noc_output_rule) |>.toAssocList,
    init_state := λ s => s = [],
  }

-- Stringify -------------------------------------------------------------------

@[drunfold] def nbag T n := nbag' T n |>.stringify

@[drunfold] def nbranch := nbranch' |>.stringify

@[drunfold] def nroute := nroute' |>.stringify

@[drunfold] def noc := noc' |>.stringify
