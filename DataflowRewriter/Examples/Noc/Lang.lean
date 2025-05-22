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
  (cur dst : RouterID' netsz) → Dir' netsz neigh cur

def Route_correct' {netsz neigh} (route : Route' netsz neigh) : Prop :=
  ∀ {cur dst}, route cur dst = DirLocal' → cur = dst

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
