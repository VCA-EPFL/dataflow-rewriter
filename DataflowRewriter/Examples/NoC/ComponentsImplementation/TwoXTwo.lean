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
import DataflowRewriter.ModuleReduction
import DataflowRewriter.ExprLow
import DataflowRewriter.ExprLowLemmas

import DataflowRewriter.Examples.NoC.Basic
import DataflowRewriter.Examples.NoC.Components
import DataflowRewriter.Examples.NoC.BasicLemmas
import DataflowRewriter.Examples.NoC.Perm

open Batteries (AssocList)

namespace DataflowRewriter.Examples.NoC.TwoXTwo

-- This file implement a non-parameterized 2x2 Noc

scoped instance TwoXTwoP : NocParam where
  Data  := ℕ
  DataS := "Nat"
  netsz := 4

-- Implementation --------------------------------------------------------------

def getX (rId : RouterID) := rId.mod 2

def getY (rId : RouterID) := rId.div 2

def arbiterXY : Arbiter := λ src dst =>
  let src_x := getX src
  let src_y := getY src
  let dst_x := getX dst
  let dst_y := getY dst
  if src_x == dst_x && src_y == dst_y then
    .some DirLocal
  else if src_x < dst_x then
    .some DirWest
  else if dst_x < src_x then
    .some DirEast
  else if src_y < dst_y then
    .some DirNorth
  else if dst_y < src_y then
    .some DirSouth
  else
    .none

def routerXY := router arbiterXY

def ε_noc : Env :=
  [
    (s!"Hide Flit 8 8", ⟨_, hide Flit 8 8⟩),      -- Hide unused i/o
    (s!"Router 0",      ⟨_, router arbiterXY 0⟩), -- Top left router
    (s!"Router 1",      ⟨_, router arbiterXY 1⟩), -- Top right router
    (s!"Router 2",      ⟨_, router arbiterXY 2⟩), -- Bot left router
    (s!"Router 3",      ⟨_, router arbiterXY 3⟩), -- Bot right router
  ].toAssocList

@[drenv] theorem hide_in_ε :
  AssocList.find? "Hide Flit 8 8" ε_noc = .some ⟨_, hide Flit 8 8⟩ := rfl

@[drenv] theorem router_in_ε_0 :
  AssocList.find? "Router 0" ε_noc = .some ⟨_, router arbiterXY 0⟩ := rfl

@[drenv] theorem router_in_ε_1 :
  AssocList.find? "Router 1" ε_noc = .some ⟨_, router arbiterXY 1⟩ := rfl

@[drenv] theorem router_in_ε_2 :
  AssocList.find? "Router 2" ε_noc = .some ⟨_, router arbiterXY 2⟩ := rfl

@[drenv] theorem router_in_ε_3 :
  AssocList.find? "Router 3" ε_noc = .some ⟨_, router arbiterXY 3⟩ := rfl

@[drunfold_defs]
def noc_low : ExprLow String :=
  let router_internal (rId : RouterID) :=
    InstIdent.internal s!"Router {rId}"

  let router_out (rId : RouterID) (dir : Dir) : InternalPort String :=
    { inst := router_internal rId, name := NatModule.stringify_output dir }

  let router_inp (rId : RouterID) (dir : Dir) : InternalPort String :=
    { inst := router_internal rId, name := NatModule.stringify_input dir }

  let mkrouter (rId : RouterID) : ExprLow String := ExprLow.base
    {
      input :=
        AssocList.cons (router_stringify_inp rId 0) (NatModule.stringify_input rId)
          (List.map
            (λ n => ⟨router_stringify_inp rId (n + 1), router_inp rId (n + 1)⟩)
            (List.range 4)
          |>.toAssocList),
      output :=
        AssocList.cons (router_stringify_out rId 0) (NatModule.stringify_output rId)
          (List.map
            (λ n => ⟨router_stringify_out rId (n + 1), router_out rId (n + 1)⟩)
            (List.range 4)
          |>.toAssocList),
    }
    s!"Router {rId}"

  -- Make a bidirectional connection between two routers
  let mkconn_bi (a b : RouterID) (portA portB : Nat) (base : ExprLow String) :=
    base |>
    ExprLow.connect { output := router_out a portA, input := router_inp b portB } |>
    ExprLow.connect { output := router_out b portB, input := router_inp a portA }

  let hide_inp (sId : Nat) : InternalPort String :=
    { inst := InstIdent.internal "Hide", name := NatModule.stringify_input sId }

  let hide_out (sId : Nat) : InternalPort String :=
    { inst := InstIdent.internal "Hide", name := NatModule.stringify_output sId }

  let mkhide : ExprLow String := ExprLow.base
    {
      input :=
        List.range 8
        |>.map (λ n => ⟨NatModule.stringify_input n, hide_inp n⟩)
        |>.toAssocList,
      output :=
        List.range 8
        |>.map (λ n => ⟨NatModule.stringify_output n, hide_out n⟩)
        |>.toAssocList,
    }
    s!"Hide Flit 8 8"

  -- Connect an output and input of a router in a direction to hide
  let mkconn_hide (rId : RouterID) (sId : Nat) (dir : Dir) (base : ExprLow String) :=
    base |>
    ExprLow.connect { output := router_out rId dir, input := hide_inp sId } |>
    ExprLow.connect { output := hide_out sId, input := router_inp rId dir }

  mkhide                          |>  -- Hide unused i/o
  ExprLow.product (mkrouter 0)    |>  -- Top left router
  ExprLow.product (mkrouter 1)    |>  -- Top right router
  ExprLow.product (mkrouter 2)    |>  -- Bot left router
  ExprLow.product (mkrouter 3)    |>  -- Bot right router
  mkconn_bi 0 1 DirEast DirWest   |>
  mkconn_bi 2 3 DirEast DirWest   |>
  mkconn_bi 0 2 DirSouth DirNorth |>
  mkconn_bi 1 3 DirSouth DirNorth |>
  mkconn_hide 0 0 DirNorth        |>
  mkconn_hide 0 1 DirWest         |>
  mkconn_hide 1 2 DirNorth        |>
  mkconn_hide 1 3 DirEast         |>
  mkconn_hide 2 4 DirSouth        |>
  mkconn_hide 2 5 DirWest         |>
  mkconn_hide 3 6 DirSouth        |>
  mkconn_hide 3 7 DirEast

def noc_lowT : Type := by
  precomputeTac [T| noc_low, ε_noc] by
    dsimp [noc_low, ε_noc]
    dsimp [ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module']
    simp (disch := simpa) only [toString, drcompute]

def_module noc_lowM : StringModule noc_lowT :=
  [e| noc_low, ε_noc]
  reduction_by
    dr_reduce_module
    simp only [drlogic]

end DataflowRewriter.Examples.NoC.TwoXTwo
