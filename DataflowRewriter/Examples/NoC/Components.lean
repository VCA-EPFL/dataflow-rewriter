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

namespace DataflowRewriter.Examples.NoC

variable [P : NocParam]

-- Utils -----------------------------------------------------------------------

-- TODO: This should be somewhere else with a better name
@[drcomponents]
def lift_f {S : Type} (n : ℕ) (f : ℕ → (Σ T : Type, S → T → S → Prop)) : PortMap ℕ (Σ T : Type, (S → T → S → Prop)) :=
  List.range n |>.map (λ i => ⟨↑i, f i⟩) |>.toAssocList

-- Components ------------------------------------------------------------------
-- Reference semantics for useful components
-- Implementation is provided in `ExprLow` and `ExprHigh` using base components

-- Branch with `n` outputs
@[drcomponents]
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

def nrouteT := List Flit

@[drcomponents]
def mk_nroute_output_rule (rID : RouterID) : (Σ T : Type, nrouteT → T → nrouteT → Prop) :=
  ⟨
    P.Data,
    λ oldState data newState => oldState = (data, { dest := rID }) :: newState
  ⟩

-- NBranch with only one input
-- TODO: This should be generalized as a `router`, which take one input
-- `P.Data × FlitHeader`, and spit out this same input on an output port based
-- on a routing function of type `FlitHeader → ...`
@[drcomponents]
def nroute' (name := "nroute") : NatModule (NatModule.Named name nrouteT) :=
  {
    inputs := [
      (0, ⟨Flit,
        λ oldState v newState => newState = oldState.concat v⟩),
    ].toAssocList,
    outputs := lift_f P.netsz mk_nroute_output_rule,
    init_state := λ s => s = [],
  }

@[drcomponents]
def mk_nbag_input_rule (S : Type) (_ : ℕ) : (Σ T : Type, List S → T → List S → Prop) :=
    ⟨S, λ oldState v newState => newState = oldState.concat v⟩

-- Bag with `n` inputs
@[drcomponents]
def nbag' (T : Type) (n : ℕ) (name := "nbag") : NatModule (NatModule.Named name (List T)) :=
  {
    inputs := lift_f n (mk_nbag_input_rule T),
    outputs := [
      (↑0, ⟨ T, λ oldState v newState =>
        ∃ i, newState = oldState.remove i ∧ v = oldState.get i ⟩)
    ].toAssocList,
    init_state := λ s => s = [],
  }

def nocT : Type :=
  List Flit

@[drcomponents]
def mk_noc_input_rule (rID : RouterID) : (Σ T : Type, nocT → T → nocT → Prop) :=
    ⟨
      Flit,
      λ oldState v newState => newState = oldState.concat v
    ⟩

@[drcomponents]
def mk_noc_output_rule (rID : RouterID) : (Σ T : Type, nocT → T → nocT → Prop) :=
    ⟨
      P.Data,
      λ oldState data newState =>
        ∃ i, newState = oldState.remove i ∧
        (data, { dest := rID }) = oldState.get i
    ⟩

@[drcomponents]
def noc' (name := "noc") : NatModule (NatModule.Named name nocT) :=
  {
    inputs := lift_f P.netsz mk_noc_input_rule,
    outputs := lift_f P.netsz mk_noc_output_rule,
    init_state := λ s => s = [],
  }

-- Stringify -------------------------------------------------------------------

@[drcomponents] def nbag T n := nbag' T n |>.stringify

@[drcomponents] def nbranch := nbranch' |>.stringify

@[drcomponents] def nroute := nroute' |>.stringify

@[drcomponents] def noc := noc' |>.stringify
