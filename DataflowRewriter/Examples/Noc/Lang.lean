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

  -- Topology definition -------------------------------------------------------

  abbrev Netsz : Type :=
    Nat

  @[simp]
  abbrev RouterID' (netsz : Netsz) : Type :=
    Fin netsz

  @[simp]
  abbrev Neigh' (netsz : Netsz) : Type :=
    RouterID' netsz → List (RouterID' netsz)

  structure Topology where
    netsz : Netsz
    neigh : Neigh' netsz

  -- Topology utils --------------------------------------------------------------

  abbrev Topology.RouterID (t : Topology) :=
    RouterID' t.netsz

  abbrev Topology.Neigh (t : Topology) :=
    Neigh' t.netsz

  -- Number of neighbors + 1 for the local output / input
  @[simp]
  abbrev Topology.Dir (t : Topology) (src : t.RouterID) : Type :=
    Fin (List.length (t.neigh src) + 1)

  def Topology.DirLocal (t : Topology) {src : t.RouterID} : t.Dir src :=
    Fin.mk 0 (by simpa)

  def Topology.out_len (t : Topology) (rid : t.RouterID) : Nat :=
    List.length (t.neigh rid)

  def Topology.inp_len (t : Topology) (rid : t.RouterID) : Nat :=
    0 -- TODO

  -- Routing policy definition -------------------------------------------------

  @[simp]
  abbrev Route' (t : Topology) (Flit : Type) : Type :=
    (cur : t.RouterID) → (flit : Flit) → (t.Dir cur × Flit)

  @[simp]
  abbrev Flit' (Data : Type) (FlitHeader : Type) : Type :=
    Data × FlitHeader

  @[simp]
  abbrev MkHead' (t : Topology) (Data : Type) (FlitHeader : Type) : Type :=
    (cur dst : t.RouterID) → (data : Data) → FlitHeader

  structure RoutingPolicy (t : Topology) (Data : Type) where
    FlitHeader  : Type
    route       : Route' t (Flit' Data FlitHeader)
    mkhead      : MkHead' t Data FlitHeader

  -- Routing policy utils ------------------------------------------------------

  variable {t : Topology} {Data : Type}

  abbrev RoutingPolicy.Flit (rp : RoutingPolicy t Data) :=
    Flit' Data rp.FlitHeader

  abbrev RoutingPolicy.Route (rp : RoutingPolicy t Data) :=
    Route' t rp.Flit

  abbrev RoutingPolicy.MkHead (rp : RoutingPolicy t Data) :=
    MkHead' t Data rp.FlitHeader

  -- Router definition ---------------------------------------------------------

  @[simp]
  abbrev NocState' (netsz : Netsz) (RouterState : Type) :=
    Vector RouterState netsz

  @[simp]
  abbrev RouterRel' (netsz : Netsz) (Flit RouterState : Type) :=
    let NocState := NocState' netsz RouterState
    let RouterID := RouterID' netsz
    (rid : RouterID) → (val : Flit) → (old_s new_s : NocState) → Prop

  structure Router (netsz : Netsz) (Flit : Type) where
    State       : Type
    init_state  : State
    input_rel   : RouterRel' netsz Flit State
    output_rel  : RouterRel' netsz Flit State

  -- Router utils --------------------------------------------------------------

  variable {netsz : Netsz} {Flit : Type}

  abbrev Router.NocState (r : Router netsz Flit) :=
    NocState' netsz r.State

  abbrev Router.RouterRel (r : Router netsz Flit) :=
    RouterRel' netsz Flit r.State

  -- Noc -----------------------------------------------------------------------

  structure Noc (Data : Type) [BEq Data] [LawfulBEq Data] where
    topology      : Topology
    routing_pol   : RoutingPolicy topology Data
    routers       : Router topology.netsz routing_pol.Flit

  variable {Data : Type} [BEq Data] [LawfulBEq Data]

end DataflowRewriter.Noc
