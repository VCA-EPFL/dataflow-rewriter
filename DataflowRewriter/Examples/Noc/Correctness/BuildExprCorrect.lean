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
    rmodT             : Type _
    rmod_homogeneous  : n.env_rmod_homogeneous rmod rmodT
    empty_in_ε        : n.env_empty ε

  variable (n : Noc Data) (ε : Env) [EC : EnvCorrect n ε]

  abbrev mod := NatModule.stringify n.build_module

  @[drunfold_defs]
  def_module expT : Type := [T| n.build_expr, ε] reduction_by
    dsimp [drunfold_defs, drcomponents]
    dsimp [ExprLow.build_module_type]
    dsimp [ExprLow.build_module]
    rw [ExprLow.build_module_connect_foldr]
    dsimp [ExprLow.build_module]
    rw [ExprLow.build_module_product_foldr]
    dsimp [ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module']
    rw [EC.empty_in_ε]
    conv =>
      pattern List.foldr _ _
      arg 2
      arg 1
      intro i acc
      rw [←router_name, EC.rmod_in_ε i]
      dsimp
    rw [Module.dep_foldr_1 (f := λ i acc => acc)]
    rw [Module.dep_foldr_1 (f := λ i acc => (EC.rmod i).1 × acc)]
    simp only [drenv, drcompute, List.foldr_fixed]
    rw [←DPListL', ←DPListL]

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
    Opaque (h.mp s.2) ↔ Opaque (⟨a', h.mp s.2⟩ : Σ T, f T).2 := by
      rfl

  -- This is very probably false…
  theorem S_eq {Ident S S' : Type _} (h : Module Ident S = Module Ident S') :
    S = S' := by
      -- f x = f y
      -- x = y
      sorry

  theorem PortMap_eq {Ident S S' : Type _} (h : Module Ident S = Module Ident S') :
    PortMap Ident (RelIO S) = PortMap Ident (RelIO S') := by
      congr; exact S_eq h

  theorem RelInt_eq {Ident S S' : Type _} (h : Module Ident S = Module Ident S') :
    List (RelInt S) = List (RelInt S') := by
      congr; exact S_eq h

  theorem S_Prop_eq {Ident S S' : Type _} (h : Module Ident S = Module Ident S') :
    (S → Prop) = (S' → Prop) := by
      congr; exact S_eq h

  -- TODO: Is this true? Is this provable?
  -- Seems fishy
  theorem mp_inputs' {Ident S S' : Type _} {m : Module Ident S} (h : Module Ident S = Module Ident S') :
    (PortMap_eq h).mpr (h.mp m).inputs = m.inputs := by
      sorry

  theorem mp_inputs {Ident S S' : Type _} {m : Module Ident S} (h : Module Ident S = Module Ident S'):
    (h.mp m).inputs = (PortMap_eq h).mp m.inputs := by sorry

  theorem mp_outputs {Ident S S' : Type _} {m : Module Ident S} (h : Module Ident S = Module Ident S'):
    (h.mp m).outputs = (PortMap_eq h).mp m.outputs := by sorry

  theorem mp_init_state {Ident S S' : Type _} {m : Module Ident S} (h : Module Ident S = Module Ident S') :
    (h.mp m).init_state = (S_Prop_eq h).mp m.init_state := by
      sorry

  theorem mp_init_state' {Ident S S' : Type _} {m : Module Ident S} (H1 : S = S') (h2 : Module Ident S = Module Ident S') :
    (h2.mp m).init_state = (S_Prop_eq h2).mp m.init_state := by
      ext f
      constructor
      · intro _; unfold S_Prop_eq; cases m; simp; sorry
      · intro _; sorry

  theorem mp_lower' {Ident S S' : Type _} {inp out int init} (h : Module Ident S = Module Ident S') :
    h.mp {
      inputs := inp,
      outputs := out,
      internals := int,
      init_state := init,
    }
    = {
        inputs := (PortMap_eq h).mp inp,
        outputs := (PortMap_eq h).mp out,
        internals := (RelInt_eq h).mp int,
        init_state := (S_Prop_eq h).mp init,
      } := by
        sorry

  theorem nil_renaming {α β} [DecidableEq α] (l : AssocList α β) :
  (AssocList.mapKey (@AssocList.nil α α).bijectivePortRenaming l) = l := by
    induction l with
    | nil => rfl
    | cons x v tl HR => simpa [HR, AssocList.bijectivePortRenaming, drcompute]

  @[drunfold_defs]
  def_module expM : Module String (expT n ε) := [e| n.build_expr, ε] reduction_by
    dsimp [drunfold_defs, reduceAssocListfind?, reduceListPartition]
    dsimp [ExprLow.build_module_expr, ExprLow.build_module_type]
    dsimp [ExprLow.build_module]
    rw [ExprLow.build_module_connect_foldr]
    dsimp [ExprLow.build_module]
    rw [ExprLow.build_module_product_foldr]
    dsimp [ExprLow.build_module, ExprLow.build_module']
    rw [EC.empty_in_ε]; dsimp
    dsimp [drcomponents]
    rw [rw_opaque (by
      conv =>
        pattern List.foldr _ _
        arg 2
        arg 1
        intro i acc
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
    have := Module.foldr_acc_plist_2
      (acc :=
        ⟨Unit, { inputs := .nil, outputs := .nil, init_state := λ x => True }⟩
      )
      (l := fin_range n.topology.netsz)
      (f := λ i acc1 => (EC.rmod i).1 × acc1)
      (g_inputs := λ i acc =>
        AssocList.mapVal (λ x => Module.liftL) ((EC.rmod i).2.inputs)
          ++ AssocList.mapVal (λ x => Module.liftR) acc.2
      )
      (g_outputs := λ i acc =>
        (AssocList.mapVal (λ x => Module.liftL) ((EC.rmod i).2.outputs))
          ++ (AssocList.mapVal (λ x => Module.liftR) acc.2)
      )
      (g_internals := λ i acc =>
            List.map Module.liftL' (EC.rmod i).2.internals
         ++ List.map Module.liftR' acc.2
      )
      (g_init_state := λ i acc =>
        λ x => (EC.rmod i).snd.init_state x.1 ∧ acc.2 x.2
      )
    rw [this]
    clear this
    rw [Module.foldr_connect']
    dsimp
    simp only [drcompute]
    -- For the init_state:
    -- We want to remove the dependent type part.
    -- This is specific to the combination of a dep_foldl to produce a PListL,
    -- but should work

    -- For inputs, outputs:
    -- We want to lower the eraseAll.
    -- It is a bit annoying to do, since erasing after a fold is rarely the same
    -- thing as erasing inside of it.
    -- Even here, there is a subtelty that we cannot make it disapear easily
    -- because otherwise we might not get the correct amount of lift…
    --
    -- What would be really nice would be to be able to transform the
    -- Module.foldl_io into a map-flatten or something...

  instance : MatchInterface (expM n ε) (mod n) := by
    apply MatchInterface_simpler
    <;> intro _
    <;> dsimp [drunfold_defs, drcomponents]
    <;> sorry

  -- TODO: Proper name
  def tmp_cast : Fin (fin_range n.topology.netsz).length = n.RouterID := by
    rw [fin_range_len]

  -- TODO: Proper name
  def tmp2 {rid : Fin (fin_range n.topology.netsz).length} :
  (EC.rmod ((fin_range n.topology.netsz).get rid)).1 =
    (EC.rmod (Fin.mk rid (by cases rid; rename_i n h; rw [fin_range_len] at h; simpa))).1 := by
      rw [fin_range_get]; rfl

  def φ (I : expT n ε) (S : n.State) : Prop :=
    ∀ (rid : n.RouterID),
      (Module.refines_refines' (EC.rmod_ok rid)).2.choose
        ((tmp2 n ε).mp
        (I.get' rid.1 (by rw [fin_range_len]; exact rid.2))) (S.get rid)

  theorem vec_rep_get {α n} {v : α} {i : Fin n} :
    (Vector.replicate n v).get i = v := by sorry

  set_option pp.proofs true in
  theorem refines_initial : Module.refines_initial (expM n ε) (mod n) (φ n ε) := by
    intro i H
    apply Exists.intro _
    apply And.intro
    · -- TODO: This work only because Noc's router initial state is just one
      -- state and not a property on state, which is quite weak.
      dsimp [drcomponents]
    · intro rid
      unfold Noc.φ._proof_1
      unfold Noc.φ._proof_2
      unfold Noc.φ._proof_3
      unfold Noc.φ._proof_5
      obtain Hspec := Exists.choose_spec ((Module.refines_refines' (EC.rmod_ok rid)).2)
      obtain ⟨Hspec1, ⟨Hspec2, Hspec3⟩⟩ := Hspec
      dsimp [Module.refines_initial] at Hspec3
      specialize Hspec3 (((tmp2 n ε).mp (i.get' rid.1 (by rw [fin_range_len]; exact rid.2))))
      specialize Hspec3 sorry -- TODO: Prove with H, annoying
      obtain ⟨s, ⟨Hs1, Hs2⟩⟩ := Hspec3
      dsimp [drcomponents] at Hs1
      subst s
      dsimp [drunfold_defs, drcomponents] at Hs2
      rw [vec_rep_get]
      exact Hs2

  theorem refines_φ : (expM n ε)  ⊑_{φ n ε} (mod n) := by
    sorry

  theorem ϕ_indistinguishable :
    ∀ i s, (φ n ε) i s → Module.indistinguishable (expM n ε) (mod n) i s := by
      sorry

  theorem correct : (expM n ε) ⊑ (mod n) := by
    apply (
      Module.refines_φ_refines
        (ϕ_indistinguishable n ε)
        (refines_initial n ε)
        (refines_φ n ε)
    )

end DataflowRewriter.Noc
