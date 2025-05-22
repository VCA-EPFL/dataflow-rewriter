/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import DataflowRewriter.Module
import DataflowRewriter.Examples.Noc.Lang

namespace DataflowRewriter.Noc.DirectedTorus

structure DirectedTorus where
  size_x : Nat
  size_y : Nat

abbrev DirectedTorus.pos_x (d : DirectedTorus) : Type :=
  Fin d.size_x

abbrev DirectedTorus.pos_y (d : DirectedTorus) : Type :=
  Fin d.size_y

def DirectedTorus.netsz (d : DirectedTorus) : Netsz' :=
  d.size_x * d.size_y

def DirectedTorus.RouterID (d : DirectedTorus) :=
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

def DirectedTorus.Route (d : DirectedTorus) :=
  Route' d.netsz d.neigh

theorem DirectedTorus.neigh_uniform (d : DirectedTorus) (src : d.RouterID) :
  (d.neigh src).length = 2 := by  simpa [DirectedTorus.neigh]

abbrev DirectedTorus.DirX (d : DirectedTorus) {src} : d.Dir src :=
  Fin.mk 1 (by simpa [DirectedTorus.neigh_uniform])

abbrev DirectedTorus.DirY (d : DirectedTorus) {src} : d.Dir src :=
  Fin.mk 2 (by simpa [DirectedTorus.neigh_uniform])

def DirectedTorus.route_xy (d : DirectedTorus) : d.Route :=
  λ src dst =>
    if d.get_x src != d.get_x dst then d.DirX
    else if d.get_y src != d.get_y dst then d.DirY
    else d.DirLocal

def DirectedTorus.xy_to_noc (d : DirectedTorus) (Data : Type) : Noc :=
  {
    netsz := d.netsz,
    neigh := d.neigh,
    route := d.route_xy,
    Data  := Data,
  }
