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

open Batteries (AssocList)

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

  @[simp]
  abbrev Neigh_ok' (netsz : Netsz) (inp : Neigh' netsz) (out : Neigh' netsz) :=
    ∀ rid rid', List.count rid' (out rid) = List.count rid (inp rid')

  structure Topology where
    netsz     : Netsz
    neigh_inp : Neigh' netsz
    neigh_out : Neigh' netsz
    neigh_ok  : Neigh_ok' netsz neigh_inp neigh_out

  abbrev Topology.RouterID (t : Topology) :=
    RouterID' t.netsz

  abbrev Topology.Neigh (t : Topology) :=
    Neigh' t.netsz

  @[simp]
  abbrev Topology.Dir_out (t : Topology) (rid : t.RouterID) : Type :=
    Fin (List.length (t.neigh_out rid) + 1)

  @[simp]
  abbrev Topology.Dir_inp (t : Topology) (rid : t.RouterID) : Type :=
    Fin (List.length (t.neigh_inp rid) + 1)

  abbrev Topology.mkDir_out (t : Topology) (rid : t.RouterID) (i : Nat) (h : i < List.length (t.neigh_out rid)) : t.Dir_out rid :=
    Fin.mk (i + 1) (by simpa)

  abbrev Topology.mkDir_inp (t : Topology) (rid : t.RouterID) (i : Nat) (h : i < List.length (t.neigh_inp rid)) : t.Dir_inp rid :=
    Fin.mk (i + 1) (by simpa)

  def Topology.DirLocal_out (t : Topology) {rid : t.RouterID} : t.Dir_out rid :=
    Fin.mk 0 (by simpa)

  def Topology.DirLocal_inp (t : Topology) {rid : t.RouterID} : t.Dir_inp rid :=
    Fin.mk 0 (by simpa)

  abbrev Topology.out_len (t : Topology) (rid : t.RouterID) : Nat :=
    (t.neigh_out rid).length

  abbrev Topology.inp_len (t : Topology) (rid : t.RouterID) : Nat :=
    (t.neigh_inp rid).length

  -- def Topology.conn (t : Topology) (rid : t.RouterID) : AssocList (t.Dir_out rid) (Σ rid' : t.RouterID, t.Dir_inp rid') :=
  --   t.neigh_out rid
  --   |>.mapFinIdx (λ dir rid' Hdir => (t.mkDir_out rid dir Hdir, ⟨rid', t.DirLocal_inp⟩))
  --   |>.toAssocList

  def Topology.conn' (t : Topology) (rid : t.RouterID) : List (Σ (rid_out rid_inp : t.RouterID), t.Dir_out rid_out × t.Dir_inp rid_inp) :=
    -- TODO: Replace t.DirLocal_inp with a proper input
    -- We need to handle the case where we have multiple connections with the
    -- same router, maybe we need an accumulator saying how many times we've
    -- encoutered stuff
    t.neigh_out rid
    |>.mapFinIdx (λ dir rid' Hdir => ⟨rid, rid', (t.mkDir_out rid dir Hdir, t.DirLocal_inp)⟩)

  abbrev Topology.conn (t : Topology) :=
    Σ (rid_out rid_inp : t.RouterID), t.Dir_out rid_out × t.Dir_inp rid_inp

  def Topology.conns (t : Topology) : List t.conn :=
    List.foldl (λ acc rid => acc ++ (t.conn' rid)) [] (fin_range t.netsz)

  -- Routing policy ------------------------------------------------------------

  @[simp]
  abbrev Route' (t : Topology) (Flit : Type) : Type :=
    (cur : t.RouterID) → (flit : Flit) → (t.Dir_out cur × Flit)

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

  variable {t : Topology} {Data : Type}

  abbrev RoutingPolicy.Flit (rp : RoutingPolicy t Data) :=
    Flit' Data rp.FlitHeader

  abbrev RoutingPolicy.Route (rp : RoutingPolicy t Data) :=
    Route' t rp.Flit

  abbrev RoutingPolicy.MkHead (rp : RoutingPolicy t Data) :=
    MkHead' t Data rp.FlitHeader

  -- Router --------------------------------------------------------------------

  -- TODO: RouterRel' sould have a `Dir_inp rid` as a parameter so we know where
  -- we got the message from
  @[simp]
  abbrev RouterRel' (netsz : Netsz) (Flit RouterState : Type) :=
    (rid : RouterID' netsz) → (old_s : RouterState) → (val : Flit) → (old_s : RouterState) → Prop

  structure Router (netsz : Netsz) (Flit : Type) where
    State       : Type
    init_state  : State
    input_rel   : RouterRel' netsz Flit State
    output_rel  : RouterRel' netsz Flit State

  abbrev Router.Rel {netsz : Netsz} {Flit : Type} (r : Router netsz Flit) :=
    RouterRel' netsz Flit r.State

  -- Noc -----------------------------------------------------------------------

  structure Noc (Data : Type) [BEq Data] [LawfulBEq Data] where
    topology      : Topology
    routing_pol   : RoutingPolicy topology Data
    routers       : Router topology.netsz routing_pol.Flit

  variable {Data : Type} [BEq Data] [LawfulBEq Data]

  @[simp]
  abbrev Noc.netsz (n : Noc Data) :=
    n.topology.netsz

  @[simp]
  abbrev Noc.State (n : Noc Data) :=
    Vector n.routers.State n.topology.netsz

  @[simp]
  abbrev Noc.RouterID (n : Noc Data) :=
    n.topology.RouterID

  @[simp]
  abbrev Noc.Dir_out (n : Noc Data) :=
    n.topology.Dir_out

  @[simp]
  abbrev Noc.Dir_inp (n : Noc Data) :=
    n.topology.Dir_inp

  @[simp]
  abbrev Noc.Flit (n : Noc Data) :=
    n.routing_pol.Flit

  @[simp]
  abbrev Noc.Rel_out (n : Noc Data) (T : Type) :=
    (rid : n.RouterID) → (dir : n.Dir_out rid) → (old_s : n.State) → (val : T) → (old_s : n.State) → Prop

  @[simp]
  abbrev Noc.Rel_inp (n : Noc Data) (T : Type) :=
    (rid : n.RouterID) → (dir : n.Dir_inp rid) → (old_s : n.State) → (val : T) → (old_s : n.State) → Prop

end DataflowRewriter.Noc
