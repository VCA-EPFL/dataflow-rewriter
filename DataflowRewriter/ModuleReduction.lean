/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Lean

import DataflowRewriter.Tactic
import DataflowRewriter.Module

open Lean.Elab.Command

macro "dr_reduce_module" : tactic =>
  return Lean.Unhygienic.run `(tactic|
     (dsimp [drunfold_defs, ExprHigh.extract, List.foldlM]
      rw [rw_opaque (by simp (disch := simp) only [drcompute, ↓reduceIte]; rfl)]
      dsimp [ ExprHigh.lower, ExprHigh.lower', ExprHigh.uncurry
            , ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module']
      rw [rw_opaque (by simp (disch := simp) only [ε, drcompute, ↓reduceIte]; rfl)]
      dsimp [drcomponents]
      dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, AssocList.bijectivePortRenaming, AssocList.invertible, AssocList.keysList, AssocList.inverse, AssocList.filterId, AssocList.filter, List.inter]; simp (disch := simp) only [drcompute, ↓reduceIte]
      dsimp [Module.product, Module.liftL, Module.liftR]
      dsimp [Module.connect']
      simp (disch := simp) only [drcompute, ↓reduceIte]
      conv =>
        pattern (occs := *) Module.connect'' _ _
        all_goals
          rw [(Module.connect''_dep_rw (h := by simp (disch := simp) only [AssocList.eraseAll_cons_neq,AssocList.eraseAll_cons_eq,AssocList.eraseAll_nil,PortMap.getIO,AssocList.find?_cons_eq,AssocList.find?_cons_neq]; dsimp -failIfUnchanged)
                                   (h' := by simp (disch := simp) only [AssocList.eraseAll_cons_neq,AssocList.eraseAll_cons_eq,AssocList.eraseAll_nil,PortMap.getIO,AssocList.find?_cons_eq,AssocList.find?_cons_neq]; dsimp -failIfUnchanged))]
      unfold Module.connect''
      dsimp -failIfUnchanged))

/--
Define a module by reducing it beforehand.
-/
elab "def_module " name:ident l:optDeclSig " := " t:term "reduction_by " tac:tacticSeq : command => do
  elabCommand <|← `(def $name $l := by precomputeTac $t by $tac)

elab "def_module " name:ident l:optDeclSig " := " t:term : command => do
  elabCommand <|← `(def_module $name $l := $t reduction_by dr_reduce_module)
