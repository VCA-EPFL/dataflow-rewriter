/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import DataflowRewriter.Module
import DataflowRewriter.Component
import DataflowRewriter.ModuleReduction
import DataflowRewriter.ExprLow
import DataflowRewriter.ExprLowLemmas

import DataflowRewriter.Examples.Noc.Basic
import DataflowRewriter.Examples.Noc.Components
import DataflowRewriter.Examples.Noc.BasicLemmas
import DataflowRewriter.Examples.Noc.Perm

open Batteries (AssocList)

namespace DataflowRewriter.Examples.Noc.TwoXTwo

variable [P : NocParam]
variable [MP : MeshParam]

-- Implementation --------------------------------------------------------------

def getX (rId : RouterID) : Nat := rId.mod MP.len

def getY (rId : RouterID) : Nat := rId.div MP.len

def rIdOfXY (X Y : Nat) :=
  Y * MP.len + X

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

@[simp] def routerXY := router arbiterXY

def hideC : Nat :=
  -- One len for each side (top, bot, left, right)
  (MP.len * 4)

def ε_noc : Env :=
  [
    -- Hide unused i/o
    (s!"Hide Flit {hideC} {hideC}", ⟨_, hide Flit hideC hideC⟩),
  ].toAssocList
  ++
  (List.map (λ i => (s!"Router {i}", ⟨_, routerXY i⟩)) (List.range P.netsz)).toAssocList

@[drenv] theorem hide_in_ε :
  AssocList.find? "Hide {hideC hideC} " ε_noc = .some ⟨_, hide Flit hideC hideC⟩ :=
  sorry

@[drenv] theorem router_in_ε_n (n : Nat) (Hok : n < P.netsz) :
  AssocList.find? "Router {n}" ε_noc = .some ⟨_, routerXY n⟩ :=
    sorry

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

  let mkrouters (base : ExprLow String) : ExprLow String :=
    List.foldl (λ acc i => ExprLow.product acc (mkrouter i)) base (List.range P.netsz)

  -- Make a bidirectional connection between two routers
  let mkconn_bi (a b : RouterID) (portA portB : Nat) (base : ExprLow String) :=
    base |>
    ExprLow.connect { output := router_out a portA, input := router_inp b portB } |>
    ExprLow.connect { output := router_out b portB, input := router_inp a portA }

  let mkconns_bi (base : ExprLow String) :=
    List.foldl (λ acc x =>
      List.foldl (λ acc y =>
        acc |>
        mkconn_bi (rIdOfXY x y) (rIdOfXY (x + 1) y) DirEast DirWest |>
        mkconn_bi (rIdOfXY x y) (rIdOfXY x (y + 1)) DirSouth DirNorth
      ) acc (List.range (MP.len - 1)))
    base (List.range (MP.len - 1))

  let hide_inp (sId : Nat) : InternalPort String :=
    { inst := InstIdent.internal "Hide", name := NatModule.stringify_input sId }

  let hide_out (sId : Nat) : InternalPort String :=
    { inst := InstIdent.internal "Hide", name := NatModule.stringify_output sId }

  let mkhide : ExprLow String := ExprLow.base
    {
      input :=
        List.range hideC
        |>.map (λ n => ⟨NatModule.stringify_input n, hide_inp n⟩)
        |>.toAssocList,
      output :=
        List.range hideC
        |>.map (λ n => ⟨NatModule.stringify_output n, hide_out n⟩)
        |>.toAssocList,
    }
    s!"Hide Flit {hideC} {hideC}"

  -- Connect an output and input of a router in a direction to hide
  let mkconn_hide (rId : RouterID) (sId : Nat) (dir : Dir) (base : ExprLow String) :=
    base |>
    ExprLow.connect { output := router_out rId dir, input := hide_inp sId } |>
    ExprLow.connect { output := hide_out sId, input := router_inp rId dir }

  let mkconns_hide (base : ExprLow String) :=
    List.foldl (λ acc i =>
      acc |>
      mkconn_hide (rIdOfXY 0 i)             (i * 4 + 0) DirWest |>
      mkconn_hide (rIdOfXY i 0)             (i * 4 + 1) DirNorth |>
      mkconn_hide (rIdOfXY (MP.len - 1) i)  (i * 4 + 2) DirEast |>
      mkconn_hide (rIdOfXY i (MP.len - 1))  (i * 4 + 3) DirSouth
    ) base (List.range MP.len)

  mkhide |>
  mkrouters |>
  mkconns_bi |>
  mkconns_hide

def noc_lowT : Type := by
  precomputeTac [T| noc_low, ε_noc] by
    dsimp [drunfold_defs, drcomponents]
    dsimp [ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module']
    unfold ExprLow.build_module'
    simp (disch := simpa) only [toString, drcompute, drenv]
    -- List.fold ...

def_module noc_lowM : StringModule noc_lowT :=
  [e| noc_low, ε_noc]
  reduction_by
    dsimp -failIfUnchanged [drunfold_defs, reduceAssocListfind?, reduceListPartition]
    dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
    dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module']
    -- rw [rw_opaque (by simp only [drenv]; rfl)]; dsimp -failIfUnchanged
    skip
    -- rfl
    -- dr_reduce_module
    -- simp only [drlogic]

end DataflowRewriter.Examples.Noc.TwoXTwo

