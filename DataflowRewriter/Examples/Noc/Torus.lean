/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import DataflowRewriter.Module
import DataflowRewriter.Examples.Noc.Lang

namespace DataflowRewriter.Noc.DirectedTorus

variable {α : Type} [BEq α] [LawfulBEq α]

structure DirectedTorus where
  size_x  : Nat
  size_y  : Nat

abbrev DirectedTorus.pos_x (d : DirectedTorus) : Type :=
  Fin d.size_x

abbrev DirectedTorus.pos_y (d : DirectedTorus) : Type :=
  Fin d.size_y

def DirectedTorus.netsz (d : DirectedTorus) : Netsz :=
  d.size_x * d.size_y

abbrev DirectedTorus.RouterID (d : DirectedTorus) :=
  RouterID' d.netsz

def DirectedTorus.Neigh (d : DirectedTorus) :=
  Neigh' d.netsz

def DirectedTorus.get_x (d : DirectedTorus) (i : d.RouterID) : d.pos_x :=
  -- TODO
  Fin.mk (i.toNat % d.size_x) (by sorry)

def DirectedTorus.get_y (d : DirectedTorus) (i : d.RouterID) : d.pos_y :=
  -- TODO
  Fin.mk ((i.toNat / d.size_x) % d.size_y) (by sorry)

def DirectedTorus.get_rid (d : DirectedTorus) (x : d.pos_x) (y : d.pos_y) : d.RouterID :=
  -- TODO
  Fin.mk (y * d.size_x + x) (by sorry)

def DirectedTorus.get_neigh_x (d : DirectedTorus) (x : d.pos_x) : d.pos_x :=
  -- TODO
  Fin.mk ((x.toNat + 1) % d.size_x) (by sorry)

def DirectedTorus.get_neigh_y (d : DirectedTorus) (y : d.pos_y) : d.pos_y :=
  -- TODO
  Fin.mk ((y.toNat + 1) % d.size_y) (by sorry)

def DirectedTorus.neigh (d : DirectedTorus) : d.Neigh :=
  λ src =>
    let src_x := d.get_x src
    let src_y := d.get_y src
    [
      d.get_rid (d.get_neigh_x src_x) src_y,
      d.get_rid src_x (d.get_neigh_y src_y),
    ]

def DirectedTorus.Dir (d : DirectedTorus) :=
  Dir' d.netsz d.neigh

def DirectedTorus.DirLocal (d : DirectedTorus) {src} : d.Dir src :=
  Fin.mk 0 (by simpa)

theorem DirectedTorus.neigh_uniform (d : DirectedTorus) (src : d.RouterID) :
  (d.neigh src).length = 2 := by simpa [DirectedTorus.neigh]

abbrev DirectedTorus.DirX (d : DirectedTorus) {src} : d.Dir src :=
  Fin.mk 1 (by simpa [DirectedTorus.neigh_uniform])

abbrev DirectedTorus.DirY (d : DirectedTorus) {src} : d.Dir src :=
  Fin.mk 2 (by simpa [DirectedTorus.neigh_uniform])

abbrev DirectedTorus.MkHead (d : DirectedTorus) (Data : Type) (FlitHeader : Type) :=
  MkHead' d.netsz Data FlitHeader

-- DirectedTorus, Absolute Header and xy routing -------------------------------

@[simp] abbrev DirectedTorus.AbsoluteHeader (d : DirectedTorus) : Type :=
  d.RouterID

abbrev DirectedTorus.AbsoluteFlit (d : DirectedTorus) : Type :=
  α × d.AbsoluteHeader

abbrev DirectedTorus.AbsoluteRoute (d : DirectedTorus) : Type :=
  Route' d.netsz d.neigh (@d.AbsoluteFlit α)

@[drunfold_defs]
def DirectedTorus.absolute_route_xy (d : DirectedTorus) : @d.AbsoluteRoute α :=
  λ cur flit =>
    if d.get_x cur != d.get_x flit.2 then (d.DirX, flit)
    else if d.get_y cur != d.get_y flit.2 then (d.DirY, flit)
    else (d.DirLocal, flit)

@[drunfold_defs]
def DirectedTorus.absolute_xy_to_noc (d : DirectedTorus) : Noc α :=
  {
    netsz       := d.netsz,
    neigh       := d.neigh,
    FlitHeader  := d.AbsoluteHeader
    route       := d.absolute_route_xy,
    mkhead      := λ _ dst _ => dst,
  }

-- DirectedTorus, Relative Header and xy routing -------------------------------

structure DirectedTorus.RelativeHeader (d : DirectedTorus) where
  diff_x : Nat
  diff_y : Nat
deriving BEq

abbrev DirectedTorus.RelativeFlit (d : DirectedTorus) : Type :=
  α × d.RelativeHeader

abbrev DirectedTorus.RelativeRoute (d : DirectedTorus) : Type :=
  Route' d.netsz d.neigh (@d.RelativeFlit α)

@[drunfold_defs]
def DirectedTorus.relative_route_xy (d : DirectedTorus) : @d.RelativeRoute α :=
  λ cur flit =>
    if 0 < flit.2.diff_x then (d.DirX, flit)
    else if 0 < flit.2.diff_y then (d.DirY, flit)
    else (d.DirLocal, flit)

@[drunfold_defs]
def DirectedTorus.relative_mkhead (d : DirectedTorus) : d.MkHead α d.RelativeHeader :=
  λ cur dst data =>
    {
      diff_x := d.get_x cur - d.get_x dst,
      diff_y := d.get_y cur - d.get_y dst,
    }

@[drunfold_defs]
def DirectedTorus.relative_xy_to_noc (d : DirectedTorus) : Noc α :=
  {
    netsz       := d.netsz,
    neigh       := d.neigh,
    FlitHeader  := d.RelativeHeader
    route       := d.relative_route_xy,
    mkhead      := d.relative_mkhead,
  }
