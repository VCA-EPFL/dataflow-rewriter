/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import DataflowRewriter.Module
import DataflowRewriter.ModuleLemmas
import DataflowRewriter.ModuleReduction
import DataflowRewriter.ExprLow
import DataflowRewriter.ExprLowLemmas
import DataflowRewriter.Component
import DataflowRewriter.Examples.Noc.Utils
import DataflowRewriter.Examples.Noc.Lang
import DataflowRewriter.Examples.Noc.Spec
import DataflowRewriter.Examples.Noc.BuildExpr

open Batteries (AssocList)

variable {Data : Type} [BEq Data] [LawfulBEq Data]

namespace DataflowRewriter.Noc

  def Noc.env_correct (n : Noc Data) (ε : Env) : Prop :=
    ∀ rid : n.topology.RouterID, ∃ rmod,
      AssocList.find? (router_name n rid) ε = .some rmod
      ∧ rmod.2 ⊑ (n.spec_router rid)

  variable (n : Noc Data)
  variable (ε : Env) (ε_ok : n.env_correct ε)

  abbrev mod := NatModule.stringify n.build_module

  def_module expT : Type := [T| n.build_expr, ε] reduction_by
    dsimp -failIfUnchanged [drunfold_defs, drcomponents, toString, reduceAssocListfind?, reduceListPartition]

  def_module expM : Module String expT := [e| n.build_expr, ε] reduction_by
    dsimp -failIfUnchanged [drunfold_defs, drcomponents, toString, reduceAssocListfind?, reduceListPartition]

  instance : MatchInterface (mod n) (expM n ε) := by
    apply MatchInterface_simpler
    <;> intro _
    <;> dsimp [drunfold_defs, drcomponents]
    <;> sorry

  def φ (I : n.State) (S : expT n ε) : Prop :=
    sorry

  theorem refines_initial :
    Module.refines_initial (mod n) (expM n ε) (φ n ε) := by
      sorry

  theorem refines_φ : (mod n) ⊑_{φ n ε} (expM n ε) := by
    sorry

  theorem ϕ_indistinguishable :
    ∀ i s, (φ n ε) i s → Module.indistinguishable (mod n) (expM n ε) i s := by
      sorry

  theorem correct : (mod n) ⊑ (expM n ε) := by
    apply (
      Module.refines_φ_refines
        (ϕ_indistinguishable n ε)
        (refines_initial n ε)
        (refines_φ n ε)
    )

end DataflowRewriter.Noc
