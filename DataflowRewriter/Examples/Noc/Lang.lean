/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import DataflowRewriter.Module
import DataflowRewriter.Component
import DataflowRewriter.Examples.Noc.Utils

set_option autoImplicit false
set_option linter.all false

namespace DataflowRewriter.Noc

-- Basic definitions -----------------------------------------------------------

abbrev Netsz' : Type :=
  Nat

abbrev RouterID' (netsz : Netsz') : Type :=
  Fin netsz

abbrev Neigh' (netsz : Netsz') : Type :=
  RouterID' netsz → List (RouterID' netsz)

abbrev Dir' (netsz : Netsz') (neigh : Neigh' netsz) (src : RouterID' netsz) : Type :=
  -- Number of neighbors + 1 for the local output / input
  Fin (List.length (neigh src) + 1)

def DirLocal' {netsz neigh src} : Dir' netsz neigh src :=
  Fin.mk 0 (by simpa)

abbrev Route' (netsz : Netsz') (neigh : Neigh' netsz) : Type :=
  (src dst : RouterID' netsz) → Dir' netsz neigh src

def Route_correct' {netsz neigh} (route : Route' netsz neigh) : Prop :=
  ∀ {src dst}, route src dst = DirLocal' → src = dst

structure Noc where
  netsz : Netsz'
  neigh : Neigh' netsz
  route : Route' netsz neigh
  Data  : Type

abbrev Noc.RouterID (n : Noc) : Type :=
  RouterID' n.netsz

abbrev Noc.Neigh (n : Noc) : Type :=
  Neigh' n.netsz

abbrev Noc.Dir (n : Noc) (src : n.RouterID) : Type :=
  Dir' n.netsz n.neigh src

abbrev Noc.DirLocal (n : Noc) {src} :=
  @DirLocal' n.netsz n.neigh src

abbrev Noc.Route (n : Noc) : Type :=
  Route' n.netsz n.neigh

abbrev Noc.Route_correct (n : Noc) : Prop :=
  Route_correct' n.route

structure Noc.FlitHeader (n : Noc) : Type :=
  dst : n.RouterID

abbrev Noc.Flit (n : Noc) :=
  n.Data × n.FlitHeader

abbrev Noc.routerT (n : Noc) :=
  List n.Flit

abbrev Noc.nocT (n : Noc) : Type :=
  Vector n.routerT n.netsz

-- Building --------------------------------------------------------------------

@[drcomponents]
def Noc.input_rel (n : Noc) (rid : n.RouterID) (val : n.Flit) (old_s new_s : n.nocT) : Prop :=
  new_s = old_s.set rid (old_s[rid] ++ [val])

@[drcomponents]
def Noc.output_rel (n : Noc) (rid : n.RouterID) (dir : n.Dir rid) (val : n.Flit) (old_s new_s : n.nocT) : Prop :=
  old_s = new_s.set rid (val :: new_s[rid]) ∧ dir = n.route rid val.2.dst

@[drcomponents]
def Noc.mk_router_input (n : Noc) (rid : n.RouterID) : RelIO n.nocT :=
  ⟨n.Flit, λ old_s inp new_s => n.input_rel rid inp old_s new_s⟩

@[drcomponents]
def Noc.mk_router_output (n : Noc) (rid : n.RouterID) (dir : n.Dir rid) : RelIO n.nocT :=
  ⟨n.Flit, λ old_s out new_s => n.output_rel rid dir out old_s new_s⟩

@[drcomponents]
def Noc.mk_router_conn (n : Noc) (rid : n.RouterID) : List (RelInt n.nocT) :=
  (n.neigh rid).mapFinIdx (λ dir rid' Hdir =>
    λ old_s new_s => ∃ val,
      -- TODO: This is wrong as is because output_rel and input_rel both
      -- contains something absolute: We are asserting that all elements are
      -- unchanged appart from one thing, which means this is false
      n.output_rel rid (Fin.mk (dir + 1) (by simpa)) val old_s new_s ∧
      n.input_rel rid' val old_s new_s)

@[drcomponents]
def Noc.build (n : Noc) : Module Nat (Vector n.routerT n.netsz) :=
  {
    inputs := RelIO.liftFinf n.netsz n.mk_router_input
    outputs := RelIO.liftFinf n.netsz (λ rid => n.mk_router_output rid n.DirLocal)
    internals := RelInt.liftFinf n.netsz n.mk_router_conn,
    init_state := λ s => s = Vector.replicate n.netsz [],
  }
