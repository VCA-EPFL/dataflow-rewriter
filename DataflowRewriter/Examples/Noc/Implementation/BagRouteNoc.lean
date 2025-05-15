/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import DataflowRewriter.Component
import DataflowRewriter.ExprLow
import DataflowRewriter.ExprLowLemmas
import DataflowRewriter.Module
import DataflowRewriter.ModuleReduction

import DataflowRewriter.Examples.Noc.Basic
import DataflowRewriter.Examples.Noc.BasicLemmas
import DataflowRewriter.Examples.Noc.Components

open Batteries (AssocList)

namespace DataflowRewriter.Examples.Noc

variable [P : NocParam]

-- Implementation --------------------------------------------------------------

def ε_noc : Env :=
  [
    (s!"NBag {P.DataS} × {FlitHeaderS} {P.netsz}", ⟨_, nbag (P.Data × FlitHeader) P.netsz⟩),
    (s!"NRoute {P.DataS} {P.netsz}", ⟨_, nroute⟩),
  ].toAssocList

@[drenv]
theorem ε_noc_nroute :
  ε_noc.find? s!"NRoute {P.DataS} {P.netsz}" = .some ⟨_, nroute⟩ := by
    sorry

@[drenv]
theorem ε_noc_nbag :
  ε_noc.find? s!"NBag {P.DataS} × {FlitHeaderS} {P.netsz}"
  = .some ⟨_, nbag (P.Data × FlitHeader) P.netsz⟩ := by
    sorry

@[drunfold_defs]
def noc_low : ExprLow String :=
  let nbag : ExprLow String := ExprLow.base
    {
      input := List.range P.netsz |>.map (λ i => ⟨
        NatModule.stringify_input i,
        NatModule.stringify_input i,
      ⟩) |>.toAssocList,
      output := [⟨
        NatModule.stringify_output 0,
        { inst := InstIdent.internal "NBag", name := NatModule.stringify_output 0 }
      ⟩].toAssocList,
    }
    s!"NBag {P.DataS} × {FlitHeaderS} {P.netsz}"
  let nroute : ExprLow String := ExprLow.base
    {
      input := [⟨
        NatModule.stringify_input 0,
        { inst := InstIdent.internal "NRoute", name := NatModule.stringify_input 0 }
      ⟩].toAssocList,
      output := List.range P.netsz |>.map (λ i => ⟨
        NatModule.stringify_output i,
        NatModule.stringify_output i,
      ⟩) |>.toAssocList,
    }
    s!"NRoute {P.DataS} {P.netsz}"
  ExprLow.connect
  {
    output := { inst := InstIdent.internal "NBag", name := NatModule.stringify_output 0 }
    input := { inst := InstIdent.internal "NRoute", name := NatModule.stringify_input 0 }
  }
  (ExprLow.product nroute nbag)

def noc_lowT : Type := by
  precomputeTac [T| noc_low, ε_noc] by
    dsimp [drunfold_defs, drcomponents]
    dsimp [ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module']
    simp (disch := simpa) only [toString, drcompute]

@[drunfold_defs]
def_module noc_lowM : StringModule noc_lowT :=
  [e| noc_low, ε_noc]
  reduction_by
    dsimp -failIfUnchanged [drunfold_defs, reduceAssocListfind?, reduceListPartition]
    dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
    dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module']
    rw [rw_opaque (by simp only [drenv]; rfl)]; dsimp -failIfUnchanged

    dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
    simp (disch := decide) only [AssocList.bijectivePortRenaming_invert]
    dsimp [Module.product]
    -- dsimp only [reduceModuleconnect'2]

    dsimp [drcomponents]
    simp only [AssocList.mapVal_mapKey, AssocList.mapVal_map_toAssocList, AssocList.mapKey_map_toAssocList]
    simp only [drcompute]
    dsimp [drcomponents, Module.liftR, Module.liftL]

    unfold Module.connect'
    simp only [drcompute, drcomponents]
    rw [AssocList.eraseAll_map_neq]
    rw [AssocList.eraseAll_map_neq]
    dsimp [AssocList.concat]
    rw [AssocList.find?_append]
    rw [AssocList.find?_map_neq, AssocList.find?_cons_eq]
    dsimp

    unfold Module.connect''
    simp only [drcompute, drlogic]

end DataflowRewriter.Examples.Noc
