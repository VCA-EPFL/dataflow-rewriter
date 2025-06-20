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

  def Noc.env_rmod_homogeneous (n : Noc Data) (rmod : n.RouterID → TModule String) (rmodS : Type _) : Prop :=
    ∀ rid : n.RouterID, (rmod rid).1 = rmodS

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
    rmod              : n.RouterID → TModule String
    rmod_ok           : n.env_rmod_ok rmod
    rmod_in_ε         : n.env_rmod_in ε rmod
    rmod_homogeneous  : n.env_rmod_homogeneous rmod n.routers.State
    empty_in_ε        : n.env_empty ε

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
    rw [Module.dep_foldl_1 (f := λ acc i => (EC.rmod i).1 × acc)]
    simp only [drenv, drcompute, List.foldl_fixed]
    conv =>
      arg 1
      arg 1
      intro acc i
      rw [EC.rmod_homogeneous]
    rw [←PListL'', PListL''_toPListL', ←PListL, fin_range_len]

  theorem f_cast {f : Type _ → Type _} {a a'} (heq : a = a') : f a = f a' :=
    by subst a; rfl

  theorem rw_opaque_fst {f : Type _ → Type _} {a b a'} (heq : a = a') :
    Opaque (@Sigma.mk _ f a b).snd ↔ Opaque (@Sigma.mk _ f a' ((f_cast heq).mp b)).snd := by
    subst a; rfl

  theorem rw_opaque_snd {f : Type _ → Type _} {a b b'} (heq : b = b') :
    Opaque (@Sigma.mk _ f a b).snd ↔ Opaque (@Sigma.mk _ f a b').snd := by
    subst b; rfl

  theorem mp_combine {T1 T2 T3 : Type _} (v : T1) (H1 : T1 = T2) (H2 : T2 = T3) :
    H2.mp (H1.mp v) = (Eq.trans H1 H2).mp v := by simpa

  theorem mp_lower {f : Type _ → Type _} {a'} {s : Σ T, f T} (h : f s.1 = f a') :
    Opaque (h.mp s.2) ↔ Opaque (⟨a', h.mp s.2⟩: Σ T, f T).2 := by
      rfl

  theorem S_eq {Ident S S' : Type _} (h : Module Ident S = Module Ident S') :
    S = S' := by sorry

  theorem PortMap_eq {Ident S S' : Type _} (h : Module Ident S = Module Ident S') :
    PortMap Ident (RelIO S) = PortMap Ident (RelIO S') := by
      congr; exact S_eq h

  theorem S_Prop_eq {Ident S S' : Type _} (h : Module Ident S = Module Ident S') :
    (S → Prop) = (S' → Prop) := by
      congr; exact S_eq h

  theorem mp_inputs {Ident S S' : Type _} {m : Module Ident S} (h : Module Ident S = Module Ident S'):
    (h.mp m).inputs = (PortMap_eq h).mp m.inputs := by sorry

  theorem mp_outputs {Ident S S' : Type _} {m : Module Ident S} (h : Module Ident S = Module Ident S'):
    (h.mp m).outputs = (PortMap_eq h).mp m.outputs := by sorry

  theorem mp_init_state {Ident S S' : Type _} {m : Module Ident S} (h : Module Ident S = Module Ident S'):
    (h.mp m).init_state = (S_Prop_eq h).mp m.init_state := by sorry

  theorem nil_renaming {α β} [DecidableEq α] (l : AssocList α β) :
  (AssocList.mapKey (@AssocList.nil α α).bijectivePortRenaming l) = l := by
    induction l with
    | nil => rfl
    | cons x v tl HR => simpa [HR, AssocList.bijectivePortRenaming, drcompute]

  @[drunfold_defs]
  def_module expM : Module String (expT n) := [e| n.build_expr, ε] reduction_by
    dsimp [drunfold_defs, reduceAssocListfind?, reduceListPartition]
    dsimp [ExprLow.build_module_expr, ExprLow.build_module_type]
    rw [ExprLow.build_module_connect_foldl]
    rw [ExprLow.build_module_product_foldl]
    dsimp [ExprLow.build_module, ExprLow.build_module']
    rw [EC.empty_in_ε]; dsimp
    dsimp [drcomponents]
    rw [rw_opaque (by
      conv =>
        pattern List.foldl _ _
        arg 2
        arg 1
        intro acc i
        rw [←router_name, EC.rmod_in_ε i]
        dsimp [Module.product]
        dsimp [
          Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts,
          Module.mapInputPorts, reduceAssocListfind?
        ]
        rw [nil_renaming]
        rw [nil_renaming]
    )]
    dsimp [
      Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts,
      Module.mapInputPorts, reduceAssocListfind?
    ]
    have := Module.foldl_acc_plist_2
      (acc :=
        ⟨Unit, { inputs := .nil, outputs := .nil, init_state := λ x => True }⟩
      )
      (l := fin_range n.topology.netsz)
      (f := λ acc1 i => (EC.rmod i).1 × acc1)
      (g_inputs := λ acc i =>
        AssocList.mapVal (λ x => Module.liftL) ((EC.rmod i).2.inputs)
          ++ AssocList.mapVal (λ x => Module.liftR) acc.2
      )
      (g_outputs := λ acc i =>
        (AssocList.mapVal (λ x => Module.liftL) ((EC.rmod i).2.outputs))
          ++ (AssocList.mapVal (λ x => Module.liftR) acc.2)
      )
      (g_internals := λ acc i =>
            List.map Module.liftL' (EC.rmod i).2.internals
         ++ List.map Module.liftR' acc.2
      )
      (g_init_state := λ acc i =>
        λ x => (EC.rmod i).snd.init_state x.1 ∧ acc.2 x.2
      )
    rw [this]
    clear this
    rw [Module.foldl_connect']
    rw [rw_opaque_fst (by
      dsimp
    )]
    rw [rw_opaque_fst (by
      conv =>
        arg 1
        arg 1
        intro acc i
        rw [EC.rmod_homogeneous]
    )]
    rw [rw_opaque_fst (by
      rw [←PListL'', PListL''_toPListL', ←PListL, fin_range_len]
    )]
    dsimp only
    rw [mp_combine]
    rw [mp_combine]
    simp only [drcompute]
    -- We want to lower the eraseAll but it is a bit annoying to do:
    -- Erasing after a fold is rarely the same thing as erasing inside of it.
    -- Even here, there is a subtelty that we cannot make it disapear easily
    -- because otherwise we might not get the correct amount of lift…
    --
    -- What would be really nice would be to be able to transform the
    -- Module.foldl_io into a map-flatten or something...

  instance : MatchInterface (mod n) (expM n ε) := by
    apply MatchInterface_simpler
    <;> intro _
    <;> dsimp [drunfold_defs, drcomponents]
    <;> sorry

  def φ (I : n.State) (S : expT n) : Prop :=
    I.toList = PListL.toList S

  theorem refines_initial : Module.refines_initial (mod n) (expM n ε) (φ n) := by
    intro i H
    exists PListL.ofVector i
    dsimp [drunfold_defs, drcomponents]
    -- Annoying: We do (cast m).init_state which we want to reduce
    -- Interesting: The following does not work
    -- rw [mp_init_state]
    sorry

  theorem refines_φ : (mod n) ⊑_{φ n} (expM n ε) := by
    sorry

  theorem ϕ_indistinguishable :
    ∀ i s, (φ n) i s → Module.indistinguishable (mod n) (expM n ε) i s := by
      sorry

  theorem correct : (mod n) ⊑ (expM n ε) := by
    apply (
      Module.refines_φ_refines
        (ϕ_indistinguishable n ε)
        (refines_initial n ε)
        (refines_φ n ε)
    )

end DataflowRewriter.Noc
