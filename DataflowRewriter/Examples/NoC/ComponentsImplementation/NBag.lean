/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import Lean
import Init.Data.BitVec.Lemmas
import Qq

import DataflowRewriter.Simp
import DataflowRewriter.Module
import DataflowRewriter.ExprLow
import DataflowRewriter.ExprLowLemmas
import DataflowRewriter.Component
import DataflowRewriter.KernelRefl
import DataflowRewriter.Reduce
import DataflowRewriter.List
import DataflowRewriter.Tactic
import DataflowRewriter.AssocList
import DataflowRewriter.ModuleReduction

import DataflowRewriter.Examples.NoC.Basic
import DataflowRewriter.Examples.NoC.BasicLemmas
import DataflowRewriter.Examples.NoC.Components

open Batteries (AssocList)

namespace DataflowRewriter.Examples.NoC

variable [P : NocParam]

def ε_nbag : Env :=
  [
    (s!"Merge' {P.DataS} {P.netsz}", ⟨_, StringModule.merge' P.Data P.netsz⟩),
    (s!"Bag {P.DataS}", ⟨_, StringModule.bag P.Data⟩),
  ].toAssocList

@[drenv]
theorem ε_nbag_merge' :
  ε_nbag.find? s!"Merge' {P.DataS} {P.netsz}" = .some ⟨_, StringModule.merge' P.Data P.netsz⟩ := by
    sorry

@[drenv]
theorem ε_nbag_bag :
  ε_nbag.find? s!"Bag {P.DataS}" = .some ⟨_, StringModule.bag P.Data⟩ := by
    sorry

@[drcomponents]
def inputGen (i : ℕ) : InternalPort String × InternalPort String :=
  ⟨
    -- Port defined in the Type (Must have inst := InstIdent.top)
    NatModule.stringify_input i,
    -- Internal name, here a top level port
    NatModule.stringify_input i,
  ⟩

@[drunfold_defs]
def nbag_low : ExprLow String :=
  let merge := ExprLow.base
    {
      input := List.range P.netsz |>.map inputGen |>.toAssocList,
      output := [⟨
        -- Port defined in the Type (Must have inst := InstIdent.top)
        NatModule.stringify_output 0,
        -- Internal name
        { inst := InstIdent.internal "Merge", name := "merge_to_bag_out" }
      ⟩].toAssocList,
    }
    s!"Merge' {P.DataS} {P.netsz}" -- Instance Type
  let bag := ExprLow.base
    {
      input := [⟨
        NatModule.stringify_input 0,
        { inst := InstIdent.internal "Bag", name := "merge_to_bag_in" }
      ⟩].toAssocList,
      output := [⟨
        NatModule.stringify_output 0,
        NatModule.stringify_output 0
      ⟩].toAssocList,
    }
    s!"Bag {P.DataS}"
  ExprLow.connect
    {
      output := {
        inst := InstIdent.internal "Merge",
        name := "merge_to_bag_out"
      },
      input := {
        inst := InstIdent.internal "Bag",
        name := "merge_to_bag_in"
      },
    }
    (ExprLow.product bag merge)

def nbag_lowT : Type := by
  precomputeTac [T| nbag_low, ε_nbag] by
    dsimp [nbag_low, ε_nbag]
    dsimp [ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module']
    simp (disch := simpa) only [toString, drcompute]

def_module nbag_lowM : StringModule nbag_lowT :=
  [e| nbag_low, ε_nbag]
  reduction_by
--     dr_reduce_module
    dsimp -failIfUnchanged [drunfold_defs, reduceAssocListfind?, reduceListPartition]
    dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
    dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module']
    rw [rw_opaque (by simp only [drenv]; rfl)]; dsimp -failIfUnchanged

    dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
    simp (disch := decide) only [AssocList.bijectivePortRenaming_invert]
    dsimp [Module.product]
    dsimp only [reduceModuleconnect'2]
    dsimp only [reduceEraseAll]
    dsimp; dsimp [reduceAssocListfind?]

    unfold Module.connect''
    simp only [drcompute, drcomponents]
    dsimp [Module.liftL, Module.liftR]

end DataflowRewriter.Examples.NoC
