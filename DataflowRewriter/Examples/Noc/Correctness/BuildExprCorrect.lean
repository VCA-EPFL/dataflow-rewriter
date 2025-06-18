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

set_option Elab.async false

namespace DataflowRewriter.Noc

  variable {Data : Type} [BEq Data] [LawfulBEq Data]

  def Noc.env_rmod_ok (n : Noc Data) (rmod : n.RouterID → TModule String) : Prop :=
    ∀ rid : n.RouterID, (rmod rid).2 ⊑ (n.spec_router rid)

  def Noc.env_rmod_ok' (n : Noc Data) (rmod : n.RouterID → TModule String) : Prop :=
    ∀ rid : n.RouterID, (n.spec_router rid) ⊑ (rmod rid).2

  -- TODO:
  -- env_rmod_ok + env_rmod_ok' means that inputs and outputs rule MUST be
  -- permutations of one another right?
  -- NO: This is false.
  -- Theorem that says that env_rmod_ok gives us that, forall rid,
  -- (rmod rid).2.inputs = RelIO.liftFinf ((n.topology.neigh_inp rid).length + 1) (n.mk_spec_router_input_rule rid)

  @[drenv]
  def Noc.env_rmod_in (n : Noc Data) (ε : Env) (rmod : n.RouterID → TModule String) : Prop :=
    ∀ rid : n.RouterID, AssocList.find? (router_name n rid) ε = .some (rmod rid)

  @[drenv]
  def Noc.env_empty (n : Noc Data) (ε : Env) : Prop :=
    AssocList.find? "empty" ε = .some ⟨Unit, StringModule.empty⟩

  class EnvCorrect (n : Noc Data) (ε : Env) where
    rmod        : n.RouterID → TModule String
    rmod_ok     : n.env_rmod_ok rmod
    rmod_in_ε   : n.env_rmod_in ε rmod
    empty_in_ε  : n.env_empty ε

  variable (n : Noc Data) (ε : Env) [EC : EnvCorrect n ε]

  abbrev mod := NatModule.stringify n.build_module

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
    rw [Module.dep_foldl_1 (f := λ acc i => acc × (EC.rmod i).1)]
    simp only [drenv, drcompute, List.foldl_fixed]

  theorem f_cast {f : Type _ → Type _} {a a'} (heq : a = a') : f a = f a' :=
    by subst a; rfl

  theorem rw_opaque_fst {f : Type _ → Type _} {a b a'} (heq : a = a') :
    Opaque (@Sigma.mk _ f a b).snd ↔ Opaque (@Sigma.mk _ f a' ((f_cast heq).mp b)).snd := by
    subst a; rfl

  -- FIXME: This is clearly false, important part is just getting the .snd at
  -- top-level
  theorem del_cast {f : Type _ → Type _} {a'} {s : Σ T, f T} (h : f s.1 = f a') :
    Opaque (h.mp s.2) ↔ Opaque s.2 := by
      sorry

  @[drunfold_defs]
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
        dsimp [Module.product]
    )]
    dsimp [drcomponents]
    dsimp [
      Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts,
      Module.mapInputPorts, reduceAssocListfind?
    ]
    have := Module.foldl_acc_plist_2
      (acc :=
        ⟨
          Unit,
          { inputs := .nil, outputs := .nil, init_state := λ x => True }
        ⟩
      )
      (l := fin_range n.topology.netsz)
      (f := λ acc1 i => acc1 × (EC.rmod i).1)
      (g_inputs := λ acc i =>
        AssocList.mapVal (λ x => Module.liftL) acc.snd ++
          AssocList.mapVal (λ x => Module.liftR)
            (AssocList.mapKey
              (AssocList.nil.bijectivePortRenaming)
              (EC.rmod i).snd.inputs)
      )
      (g_outputs := λ acc i =>
        AssocList.mapVal (fun x => Module.liftL) acc.snd ++
          AssocList.mapVal (fun x => Module.liftR)
            (AssocList.mapKey
              (AssocList.nil.bijectivePortRenaming)
              (EC.rmod i).snd.outputs)
      )
      (g_internals := λ acc i =>
        List.map Module.liftL' acc.snd ++ List.map Module.liftR' (EC.rmod i).snd.internals
      )
      (g_init_state := λ acc i =>
        λ x => acc.snd x.1 ∧ (EC.rmod i).snd.init_state x.2
      )
    rw [this]
    clear this
    rw [rw_opaque_fst (by
      rw [Module.dep_foldl_1 (f := λ acc i => acc), List.foldl_fixed]
    )]
    dsimp only
    rw [del_cast]
    rw [Module.foldl_connect']
    simp only [drcompute]
    -- We should be able to say that inupts and outputs are just inputs and
    -- outputs and that we removed every internal inputs and output

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
