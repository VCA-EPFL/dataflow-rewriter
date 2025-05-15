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

import DataflowRewriter.Examples.Noc.Basic

namespace DataflowRewriter.Examples.Noc

variable [P : NocParam]

-- Utils -----------------------------------------------------------------------

-- TODO: This should be somewhere else with a better name
@[drcomponents]
def lift_f {S : Type} (n : ℕ) (f : ℕ → (Σ T : Type, S → T → S → Prop)) : PortMap ℕ (Σ T : Type, (S → T → S → Prop)) :=
  List.range n |>.map (λ i => ⟨↑i, f i⟩) |>.toAssocList

-- Utils components ------------------------------------------------------------

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
            { dst := routerID } :: newRouterIDs = oldRouterIDs
        ⟩)
      |>.toAssocList,
    init_state := λ s => s = ⟨[], []⟩,
  }

@[drcomponents] def nbranch := nbranch' |>.stringify

@[simp] abbrev nrouteT := List Flit

@[drcomponents]
def mk_nroute_output_rule (rID : RouterID) : (Σ T : Type, nrouteT → T → nrouteT → Prop) :=
  ⟨Flit, λ oldS v newS => v.2.dst = rID ∧ oldS = v :: newS⟩

-- NBranch with only one input
-- TODO: This should be generalized as a `router`, which take one input
-- `P.Data × FlitHeader`, and spit out this same input on an output port based
-- on a routing function of type `FlitHeader → ...`
@[drcomponents]
def nroute' (name := "nroute") : NatModule (NatModule.Named name nrouteT) :=
  {
    inputs := [
      (0, ⟨Flit,
        λ oldS v newS => newS = oldS.concat v⟩),
    ].toAssocList,
    outputs := lift_f P.netsz mk_nroute_output_rule,
    init_state := λ s => s = [],
  }

@[drcomponents] def nroute := nroute' |>.stringify

@[drcomponents]
def mk_nbag_input_rule (S : Type) (_ : ℕ) : (Σ T : Type, List S → T → List S → Prop) :=
    ⟨S, λ oldS v newS => newS = oldS.concat v⟩

-- Bag with `n` inputs
@[drcomponents]
def nbag' (T : Type) (n : ℕ) (name := "nbag") : NatModule (NatModule.Named name (List T)) :=
  {
    inputs := lift_f n (mk_nbag_input_rule T),
    outputs := [
      (↑0, ⟨ T, λ oldS v newS =>
        ∃ i, newS = oldS.remove i ∧ v = oldS.get i ⟩)
    ].toAssocList,
    init_state := λ s => s = [],
  }

@[drcomponents] def nbag T n := nbag' T n |>.stringify

-- Contrary to a `sink`, a `hide` never consume its i/o
@[drcomponents]
def hide' (T : Type _) (inp_sz out_sz : Nat) (name := "hide") : NatModule (NatModule.Named name Unit) :=
  {
    inputs := List.range inp_sz |>.map (λ n => ⟨n, ⟨T, λ _ _ _ => False⟩⟩) |>.toAssocList,
    outputs := List.range out_sz |>.map (λ n => ⟨n, ⟨T, λ _ _ _ => False⟩⟩) |>.toAssocList,
    init_state := λ _ => True,
  }

@[drcomponents] def hide T inp_sz out_sz := hide' T inp_sz out_sz |>.stringify

-- Network Components ----------------------------------------------------------

@[simp] abbrev nocT : Type :=
  List Flit

@[drcomponents]
def mk_noc_input_rule (rId : RouterID) : (Σ T : Type, nocT → T → nocT → Prop) :=
    ⟨
      Flit,
      λ oldS v newS => newS = oldS ++ [v]
    ⟩

@[drcomponents]
def mk_noc_output_rule (rId : RouterID) : (Σ T : Type, nocT → T → nocT → Prop) :=
    ⟨
      Flit,
      λ oldS v newS =>
        v.2.dst = rId ∧ ∃ i, newS = oldS.remove i ∧ v = oldS.get i
    ⟩

@[drcomponents]
def noc' (name := "noc") : NatModule (NatModule.Named name nocT) :=
  {
    inputs := lift_f P.netsz mk_noc_input_rule,
    outputs := lift_f P.netsz mk_noc_output_rule,
    init_state := λ s => s = [],
  }

@[drcomponents] def noc := noc' |>.stringify

@[simp] abbrev routerT := List Flit

@[drcomponents]
def mk_router_input (rId : ℕ) : Σ T : Type, routerT → T → routerT → Prop :=
  ⟨Flit, λ oldS inp newS => newS = oldS ++ [inp]⟩

@[drcomponents]
def mk_router_output (arbiter : Arbiter) (rId : RouterID) (n : ℕ) : Σ T : Type, routerT → T → routerT → Prop :=
  ⟨Flit, λ oldS out newS => oldS = out :: newS ∧ arbiter rId out.2.dst = n⟩

@[drcomponents]
def router' (arbiter : Arbiter) (rId : RouterID) (name := "router") : NatModule (NatModule.Named name nocT) :=
  {
    inputs := lift_f 5 mk_router_input,
    outputs := lift_f 5 (mk_router_output arbiter rId),
    init_state := λ s => s = [],
  }

@[drcomponents]
def router_stringify_inp (rId : RouterID) (n : ℕ) :=
  s!"Router {rId} in{n + 1}"

@[drcomponents]
def router_stringify_out (rId : RouterID) (n : ℕ) :=
  s!"Router {rId} out{n + 1}"

@[drcomponents]
def router (arbiter : Arbiter) (rId : RouterID) (name := "router") : StringModule (NatModule.Named name nocT) :=
  router' arbiter rId |>.mapIdent (router_stringify_inp rId) (router_stringify_out rId)
