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

abbrev Netsz : Type :=
  Nat

abbrev RouterID' (netsz : Netsz) : Type :=
  Fin netsz

abbrev Neigh' (netsz : Netsz) : Type :=
  RouterID' netsz → List (RouterID' netsz)

-- Number of neighbors + 1 for the local output / input
abbrev Dir' (netsz : Netsz) (neigh : Neigh' netsz) (src : RouterID' netsz) : Type :=
  Fin (List.length (neigh src) + 1)

def DirLocal' {netsz neigh src} : Dir' netsz neigh src :=
  Fin.mk 0 (by simpa)

abbrev Flit' (Data : Type) (FlitHeader : Type) : Type :=
  Data × FlitHeader

abbrev Route' (netsz : Netsz) (neigh : Neigh' netsz) (Flit : Type) : Type :=
  (cur : RouterID' netsz) → (flit : Flit) → (Dir' netsz neigh cur × Flit)

abbrev MkHead' (netsz : Netsz) (Data : Type) (FlitHeader : Type) : Type :=
  (cur dst : RouterID' netsz) → (data : Data) → FlitHeader

structure Noc (Data : Type) [BEq Data] [LawfulBEq Data] where
  netsz         : Netsz
  neigh         : Neigh' netsz
  FlitHeader    : Type
  FlitHeaderBEq : BEq FlitHeader := by exact inferInstance
  FlitHeaderEq  : LawfulBEq FlitHeader := by exact inferInstance
  mkhead        : MkHead' netsz Data FlitHeader
  route         : Route' netsz neigh (Flit' Data FlitHeader)

variable {α : Type} [BEq α] [LawfulBEq α]

abbrev Noc.Data (_ : Noc α) : Type :=
  α

abbrev Noc.RouterID (n : Noc α) : Type :=
  RouterID' n.netsz

abbrev Noc.Neigh (n : Noc α) : Type :=
  Neigh' n.netsz

abbrev Noc.Dir (n : Noc α) (src : n.RouterID) : Type :=
  Dir' n.netsz n.neigh src

abbrev Noc.DirLocal (n : Noc α) {src} :=
  @DirLocal' n.netsz n.neigh src

abbrev Noc.Route (n : Noc α) : Type :=
  Route' n.netsz n.neigh n.FlitHeader

abbrev Noc.MkHead (n : Noc α) : Type :=
  MkHead' n.netsz n.Data n.FlitHeader

abbrev Noc.Flit (n : Noc α) :=
  Flit' n.Data n.FlitHeader
