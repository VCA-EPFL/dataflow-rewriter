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

namespace DataflowRewriter.Examples.Noc.NumXNum

variable [P : NocParam]

-- Implementation --------------------------------------------------------------

@[simp, drcomponents] def routerXY := router arbiter_xy

def hideC : Nat :=
  -- One len for each side (top, bot, left, right)
  (P.len * 4)

def ε_noc : Env :=
  [
    -- Hide unused i/o
    (s!"Hide Flit {hideC} {hideC}", ⟨_, hide Flit hideC hideC⟩),
  ].toAssocList
  ++
  (List.map (λ i => (s!"Router {i}", ⟨_, routerXY i⟩)) (List.range P.netsz)).toAssocList

@[drenv]
theorem hide_in_ε_noc :
  AssocList.find? s!"Hide Flit {hideC} {hideC}" ε_noc = .some ⟨_, hide Flit hideC hideC⟩ :=
    sorry

-- TODO: False without Hok
@[drenv]
theorem router_in_ε_noc (n : RouterID) : -- (Hok : n < P.netsz) :
  AssocList.find? s!"Router {n}" ε_noc = .some ⟨_, routerXY n⟩ :=
    sorry

-- Mesh ------------------------------------------------------------------------

@[drunfold_defs]
def mesh : ExprLow String :=
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

  mkhide |>
  mkrouters

def meshT : Type := by
  precomputeTac [T| mesh, ε_noc] by
    dsimp [drunfold_defs, drcomponents]
    dsimp [ExprLow.build_module_type]
    rw [ExprLow.build_module_foldl]
    rw [Module.foldl_acc_plist]
    dsimp [ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module']
    simp only [drenv, drcompute]

def_module meshM : StringModule meshT := [e| mesh, ε_noc]
  reduction_by
    dsimp -failIfUnchanged [drunfold_defs, reduceAssocListfind?, reduceListPartition]
    dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
    dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type]
    rw [ExprLow.build_module_foldl]
    dsimp [ExprLow.build_module, ExprLow.build_module']
    rw [rw_opaque (by simp only [drenv]; rfl)]
    -- TODO: Not in the simp onyl [drenv] for some reason?
    -- Probably a dependent type issue
    rw [rw_opaque (by
      conv =>
        pattern List.foldl _ _
        arg 1
        pattern (⟨_, _⟩: TModule1 String)
        rw [router_in_ε_noc]
    )]
    dsimp [drcomponents]
    dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
    dsimp [Module.product]
    rw [rw_opaque (by
      conv =>
        pattern List.foldl _ _
        arg 1
        pattern (⟨_, _⟩: TModule1 String)
        simp only [drcompute, drcomponents]
        dsimp [Module.liftR, Module.liftL]
        -- TODO: Fix the following
        -- dsimp [List.range, List.range.loop]
        -- pattern AssocList.bijectivePortRenaming _ _
        -- simp [toString]
        -- simp (disch := decide) only [AssocList.bijectivePortRenaming_invert]
    )]
    -- TODO: We just need to simplify bijectivePortRenaming here and above
    -- We can probably have a thing similar to type where we move the fold
    -- inside of the inputs, outputs, internals and init_state

-- NoC: Connected Mesh ---------------------------------------------------------

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
        mkconn_bi (rid_of_xy x y) (rid_of_xy (x + 1) y) DirEast DirWest |>
        mkconn_bi (rid_of_xy x y) (rid_of_xy x (y + 1)) DirSouth DirNorth
      ) acc (List.range (P.len - 1)))
    base (List.range (P.len - 1))

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
  let mkconn_hide (sId : Nat) (rId : RouterID) (dir : Dir) (base : ExprLow String) :=
    base |>
    ExprLow.connect { output := router_out rId dir, input := hide_inp sId } |>
    ExprLow.connect { output := hide_out sId, input := router_inp rId dir }

  let mkconns_hide (base : ExprLow String) :=
    List.foldl (λ acc i =>
      acc |>
      mkconn_hide (i * 4 + 0) (rid_of_xy 0 i) DirWest |>
      mkconn_hide (i * 4 + 1) (rid_of_xy i 0) DirNorth |>
      mkconn_hide (i * 4 + 2) (rid_of_xy (P.len - 1) i) DirEast |>
      mkconn_hide (i * 4 + 3) (rid_of_xy i (P.len - 1)) DirSouth
    ) base (List.range P.len)

  mkhide |>
  mkrouters |>
  mkconns_bi |>
  mkconns_hide

def noc_lowT : Type := by
  precomputeTac [T| noc_low, ε_noc] by
    dsimp [drunfold_defs, drcomponents]
    dsimp [ExprLow.build_module_type]
    simp (disch := simpa) only [toString, drcompute, drenv]
    unfold ExprLow.build_module'
    -- List.fold ...

def_module noc_lowM : StringModule noc_lowT := [e| noc_low, ε_noc]
  reduction_by
    dsimp -failIfUnchanged [drunfold_defs, reduceAssocListfind?, reduceListPartition]
    dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
    dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module']
    -- rw [rw_opaque (by simp only [drenv]; rfl)]; dsimp -failIfUnchanged
    skip
    -- rfl
    -- dr_reduce_module
    -- simp only [drlogic]

end DataflowRewriter.Examples.Noc.NumXNum
