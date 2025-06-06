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

namespace DataflowRewriter.Noc

  variable {Data : Type} [BEq Data] [LawfulBEq Data]

  def Noc.env_rmod_ok (n : Noc Data) (rmod : TModule String) : Prop :=
    ∀ rid : n.RouterID, rmod.2 ⊑ (n.spec_router rid)

  @[drenv]
  def Noc.env_rmod_in (n : Noc Data) (ε : Env) (rmod : TModule String) : Prop :=
    ∀ rid : n.RouterID, AssocList.find? (router_name n rid) ε = .some rmod

  @[drenv]
  def Noc.env_empty (n : Noc Data) (ε : Env) : Prop :=
    AssocList.find? "empty" ε = .some ⟨Unit, StringModule.empty⟩

  class EnvCorrect (n : Noc Data) (ε : Env) where
    rmod        : TModule String
    rmod_ok     : n.env_rmod_ok rmod
    rmod_in_ε   : n.env_rmod_in ε rmod
    empty_in_ε  : n.env_empty ε

  variable (n : Noc Data) (ε : Env) [EC : EnvCorrect n ε]

  abbrev mod := NatModule.stringify n.build_module

  theorem tmodule_renamePorts_1 {Ident} [DecidableEq Ident] (a : TModule Ident) (p : PortMapping Ident) :
     (⟨a.1, a.2.renamePorts p⟩ : TModule Ident).1 = a.1 := by rfl

  theorem tmodule_renamePorts_2 {Ident} [DecidableEq Ident] (a : TModule Ident) (p : PortMapping Ident) :
     (⟨a.1, a.2.renamePorts p⟩ : TModule Ident).2 = a.2.renamePorts p := by rfl

  def_module expT : Type := [T| n.build_expr, ε] reduction_by
    dsimp [drunfold_defs, drcomponents]
    dsimp [ExprLow.build_module_type]
    rw [ExprLow.build_module_connect_foldl]
    rw [ExprLow.build_module_product_foldl]
    dsimp [ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module']
    rw [EC.empty_in_ε]
    conv =>
      pattern List.foldl _ _
      arg 2
      arg 1
      intro acc i
      rw [←router_name, EC.rmod_in_ε i]
      dsimp
    rw [Module.dep_foldl_1 (f := λ acc i => acc)]
    rw [Module.dep_foldl_1 (f := λ acc i => acc × (EnvCorrect.rmod n ε).1)]
    simp only [drenv, drcompute, List.foldl_fixed]

  def_module expM : Module String (expT n ε) := [e| n.build_expr, ε] reduction_by
    dsimp [drunfold_defs, reduceAssocListfind?, reduceListPartition]
    dsimp [ExprLow.build_module_expr, ExprLow.build_module_type]
    rw [ExprLow.build_module_connect_foldl]
    rw [ExprLow.build_module_product_foldl]
    dsimp [ExprLow.build_module, ExprLow.build_module']
    rw [EC.empty_in_ε]; dsimp
    rw [rw_opaque (by
      conv =>
        pattern List.foldl _ _
        arg 2
        arg 1
        intro acc i
        rw [←router_name, EC.rmod_in_ε i]
        dsimp
    )]
    dsimp [drcomponents]
    dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
    dsimp [Module.product]
    -- We need a thing like Module.foldl_acc_plist but for .snd, where we have
    -- inputs, outputs each expressed with their own fold (Lowering it)
    -- This could then allow us to simplify the top level fold doing connections
    -- in a similar way

  instance : MatchInterface (mod n) (expM n ε) := by
    apply MatchInterface_simpler
    <;> intro _
    <;> dsimp [drunfold_defs, drcomponents]
    <;> sorry

  def φ (I : n.State) (S : expT n ε) : Prop :=
    sorry

  theorem refines_initial : Module.refines_initial (mod n) (expM n ε) (φ n ε) := by
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
