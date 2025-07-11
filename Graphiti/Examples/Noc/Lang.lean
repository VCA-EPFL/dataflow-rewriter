/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import Graphiti.Module
import Graphiti.Component
import Graphiti.Examples.Noc.Utils

set_option autoImplicit false
set_option linter.all false

open Batteries (AssocList)

namespace Graphiti.Noc

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

  structure Topology (netsz : Netsz) where
    neigh_inp : Neigh' netsz
    neigh_out : Neigh' netsz
    neigh_ok  : Neigh_ok' netsz neigh_inp neigh_out

  variable {netsz : Netsz}

  abbrev Topology.RouterID (t : Topology netsz) :=
    RouterID' netsz

  abbrev Topology.Neigh (t : Topology netsz) :=
    Neigh' netsz

  @[simp]
  abbrev Topology.Dir_out (t : Topology netsz) (rid : t.RouterID) : Type :=
    Fin (List.length (t.neigh_out rid) + 1)

  @[simp]
  abbrev Topology.Dir_inp (t : Topology netsz) (rid : t.RouterID) : Type :=
    Fin (List.length (t.neigh_inp rid) + 1)

  abbrev Topology.mkDir_out (t : Topology netsz) (rid : t.RouterID) (i : Nat) (h : i < List.length (t.neigh_out rid)) : t.Dir_out rid :=
    ⟨i + 1, by simpa only [Nat.add_lt_add_iff_right]⟩

  abbrev Topology.mkDir_inp (t : Topology netsz) (rid : t.RouterID) (i : Nat) (h : i < List.length (t.neigh_inp rid)) : t.Dir_inp rid :=
    ⟨i + 1, by simpa only [Nat.add_lt_add_iff_right]⟩

  def Topology.DirLocal_out (t : Topology netsz) {rid : t.RouterID} : t.Dir_out rid :=
    ⟨0, by simpa only [Nat.zero_lt_succ]⟩

  def Topology.DirLocal_inp (t : Topology netsz) {rid : t.RouterID} : t.Dir_inp rid :=
    ⟨0, by simp only [Nat.zero_lt_succ]⟩

  abbrev Topology.out_len (t : Topology netsz) (rid : t.RouterID) : Nat :=
    (t.neigh_out rid).length

  abbrev Topology.inp_len (t : Topology netsz) (rid : t.RouterID) : Nat :=
    (t.neigh_inp rid).length

  abbrev Topology.conn (t : Topology netsz) :=
    Σ (rid_out rid_inp : t.RouterID), t.Dir_out rid_out × t.Dir_inp rid_inp

  def Topology.conn' (t : Topology netsz) (rid : t.RouterID) : List t.conn :=
    -- TODO: Replace t.DirLocal_inp with a proper input
    -- We need to handle the case where we have multiple connections with the
    -- same router, maybe we need an accumulator saying how many times we've
    -- encoutered stuff
    t.neigh_out rid
    |>.mapFinIdx (λ dir rid' Hdir => ⟨rid, rid', (t.mkDir_out rid dir Hdir, t.DirLocal_inp)⟩)


  def Topology.conns (t : Topology netsz) : List t.conn :=
    List.map t.conn' (fin_range netsz) |>.flatten

  -- Routing policy ------------------------------------------------------------

  @[simp]
  abbrev Route' (t : Topology netsz) (Flit : Type) : Type :=
    (cur : t.RouterID) → (flit : Flit) → (t.Dir_out cur × Flit)

  @[simp]
  abbrev Flit' (Data : Type) (FlitHeader : Type) : Type :=
    Data × FlitHeader

  @[simp]
  abbrev MkHead' (t : Topology netsz) (Data : Type) (FlitHeader : Type) : Type :=
    (cur dst : t.RouterID) → (data : Data) → FlitHeader

  structure RoutingPolicy (t : Topology netsz) (Data : Type) where
    FlitHeader  : Type
    route       : Route' t (Flit' Data FlitHeader)
    mkhead      : MkHead' t Data FlitHeader

  variable {t : Topology netsz} {Data : Type}

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

  structure Noc (Data : Type) [BEq Data] [LawfulBEq Data] (netsz : Netsz) where
    topology    : Topology netsz
    routing_pol : RoutingPolicy topology Data
    routers     : Router netsz routing_pol.Flit

  variable {Data : Type} [BEq Data] [LawfulBEq Data] {netsz : Netsz}

  @[simp]
  abbrev Noc.State (n : Noc Data netsz) :=
    Vector n.routers.State netsz

  @[simp]
  abbrev Noc.RouterID (n : Noc Data netsz) :=
    n.topology.RouterID

  @[simp]
  abbrev Noc.Dir_out (n : Noc Data netsz) :=
    n.topology.Dir_out

  @[simp]
  abbrev Noc.Dir_inp (n : Noc Data netsz) :=
    n.topology.Dir_inp

  @[simp]
  abbrev Noc.Flit (n : Noc Data netsz) :=
    n.routing_pol.Flit

  @[simp]
  abbrev Noc.Rel_out (n : Noc Data netsz) (T : Type) :=
    (rid : n.RouterID) → (dir : n.Dir_out rid) → (old_s : n.State) → (val : T) → (old_s : n.State) → Prop

  @[simp]
  abbrev Noc.Rel_inp (n : Noc Data netsz) (T : Type) :=
    (rid : n.RouterID) → (dir : n.Dir_inp rid) → (old_s : n.State) → (val : T) → (old_s : n.State) → Prop

end Graphiti.Noc
