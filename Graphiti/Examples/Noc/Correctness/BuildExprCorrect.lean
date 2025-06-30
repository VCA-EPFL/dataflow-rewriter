/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import Graphiti.Module
import Graphiti.ModuleLemmas
import Graphiti.ModuleReduction
import Graphiti.ExprLow
import Graphiti.ExprLowLemmas
import Graphiti.Component
import Graphiti.Examples.Noc.Utils
import Graphiti.Examples.Noc.Lang
import Graphiti.Examples.Noc.Spec
import Graphiti.Examples.Noc.Tactic
import Graphiti.Examples.Noc.BuildExpr

open Batteries (AssocList)

set_option Elab.async false

namespace Graphiti.Noc

  variable {Data : Type} [BEq Data] [LawfulBEq Data] {netsz : Netsz}

  def Noc.env_rmod_ok (n : Noc Data netsz) (rmod : n.RouterID → TModule String) : Prop :=
    ∀ rid : n.RouterID, (rmod rid).2 ⊑ (n.spec_router rid)

  def Noc.env_rmod_ok' (n : Noc Data netsz) (rmod : n.RouterID → TModule String) : Prop :=
    ∀ rid : n.RouterID, (n.spec_router rid) ⊑ (rmod rid).2

  @[drenv]
  def Noc.env_rmod_in (n : Noc Data netsz) (ε : Env) (rmod : n.RouterID → TModule String) : Prop :=
    ∀ rid : n.RouterID, AssocList.find? (router_name n rid) ε = .some (rmod rid)

  @[drenv]
  def Noc.env_empty (n : Noc Data netsz) (ε : Env) : Prop :=
    AssocList.find? "empty" ε = .some ⟨Unit, StringModule.empty⟩

  class EnvCorrect (n : Noc Data netsz) (ε : Env) where
    rmod        : n.RouterID → TModule String
    rmod_ok     : n.env_rmod_ok rmod
    rmod_in_ε   : n.env_rmod_in ε rmod
    rmodT       : Type _
    empty_in_ε  : n.env_empty ε

  variable (n : Noc Data netsz) (ε : Env) [EC : EnvCorrect n ε]

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
    rw [←DPList', ←DPList]

  theorem nil_renaming {α β} [DecidableEq α] (l : AssocList α β) :
  (AssocList.mapKey (@AssocList.nil α α).bijectivePortRenaming l) = l := by
    induction l with
    | nil => rfl
    | cons x v tl HR => simpa [HR, AssocList.bijectivePortRenaming, drcompute]

  -- theorem magic {T₁ T₁' T₂} {h : T₁ = T₁'} {t : T₁} {f : T₁' → T₂}
  --   : f (h.mp t) = (f t) := by sorry

  -- f : (α → β) → α → β
  -- theorem magic {α α' β} {h : α = α'} {f : (α → β) → α → α}
  -- (h : α = α') : f p (h.mp v) = h.mpr (f (λ i => h.mp i) v)

  theorem eraseAll_depfoldr {α β δ} [DecidableEq α] (l : List δ) (p : α → Bool) (f : δ → Type → Type) (g : δ → AssocList α β) h acc :
      AssocList.eraseAllP (λ k _ => p k)
        (
          List.foldr
          (λ i acc => (⟨f i acc.1, (g i) ++ (acc.2.mapVal h)⟩: Σ T, AssocList α β))
          acc
          l
        ).snd
      =
        (List.foldr
          (λ i acc => ⟨f i acc.1, AssocList.eraseAllP (λ k _ => p k) (g i) ++ (acc.2.mapVal h)⟩)
          (⟨acc.1, AssocList.eraseAllP (λ k _ => p k) acc.2⟩: Σ T, AssocList α β)
          l).snd
      := by
    induction l generalizing acc with
    | nil => rfl
    | cons hd tl HR =>
      dsimp; rw [←HR, AssocList.eraseAllP_concat, AssocList.eraseAllP_map_comm]

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
      (l := fin_range netsz)
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
    -- Casts in i/o forbid us from anything, we must make them at top-level
    -- rw [eraseAll_depfoldr]

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
  def tmp_cast : Fin (fin_range netsz).length = n.RouterID := by
    rw [fin_range_len]

  -- TODO: Proper name
  def tmp2 {rid : Fin (fin_range netsz).length} :
  (EC.rmod ((fin_range netsz).get rid)).1 =
    (EC.rmod (Fin.mk rid (by cases rid; rename_i n h; rw [fin_range_len] at h; simpa))).1 := by
      rw [fin_range_get]; rfl

  def I_cast_get (I : expT n ε) (rid : n.RouterID) :=
    ((tmp2 n ε).mp (I.get' rid.1 (by rw [fin_range_len]; exact rid.2)))

  def φ (I : expT n ε) (S : n.State) : Prop :=
    ∀ (rid : n.RouterID),
      (Module.refines_refines' (EC.rmod_ok rid)).2.choose
        (I_cast_get n ε I rid)
        (S.get rid)

  -- def r_noc : Noc Data (netsz - 1) :=
  --   let _ := n
  --   {
  --     topology := sorry
  --     routing_pol := sorry
  --     routers := sorry
  --   }
  --
  -- instance : EnvCorrect (r_noc n) ε := by sorry
  --
  -- def r_noc_init :
  --   ∀ (rid : (r_noc n).RouterID) (i : (EnvCorrect.rmod ε rid).fst),
  --   (EnvCorrect.rmod ε rid).snd.init_state i →
  --   (EC.rmod _).snd.init_state i := by sorry

  -- set_option pp.proofs true in
  def i_init_rid (i : expT n ε) (Hinit : (expM n ε).init_state i) :
    ∀ (rid : n.RouterID), (EC.rmod rid).2.init_state (I_cast_get n ε i rid) := by
      dsimp [drunfold_defs] at Hinit i
      revert n

      induction netsz with
      | zero => intro _ _ _ _ ⟨_, _⟩; contradiction
      | succ netsz' HR =>
        dsimp [drcomponents, drunfold_defs] at *
        intro n EC i Hinit ⟨ridv, Hrid⟩
        induction ridv with
        | zero =>
          -- TODO: This is true and should be provable but there is a lot of
          -- annoying casts to handle everywhere
          sorry
        | succ ridv' HR' =>
          rw [add_lt_add_iff_right] at Hrid
          -- FIXME: Process desribed below is not possible, init_state might
          -- depend on the total number of router in the system, this is very
          -- annoying
          -- TODO: Trick here is probably to define a new noc but with one less
          -- router so that we can use HR with this new noc.
          -- This new noc will probably be also useful down the line for proving
          -- other rules by induction, so this seems kind of like a custom
          -- induction hypothesis
          sorry

  set_option pp.proofs true in
  theorem refines_initial : Module.refines_initial (expM n ε) (mod n) (φ n ε) := by
    intro i H
    apply Exists.intro _
    apply And.intro
    · -- NOTE: This work only because Noc's router initial state is just one
      -- state and not a property on state, which is quite weak.
      dsimp [drcomponents]
    · intro rid
      obtain Hspec := Exists.choose_spec ((Module.refines_refines' (EC.rmod_ok rid)).2)
      obtain ⟨Hspec1, ⟨Hspec2, Hspec3⟩⟩ := Hspec
      dsimp [Module.refines_initial] at Hspec3
      specialize Hspec3 (I_cast_get n ε i rid)
      apply i_init_rid at H
      specialize H rid
      unfold I_cast_get at Hspec3
      specialize Hspec3 H
      obtain ⟨s, ⟨Hs1, Hs2⟩⟩ := Hspec3
      dsimp [drcomponents] at Hs1
      subst s
      dsimp [drunfold_defs, drcomponents] at Hs2
      rw [Vector.get_replicate]
      exact Hs2

  theorem refines_φ : (expM n ε) ⊑_{φ n ε} (mod n) := by
    sorry

  theorem ϕ_indistinguishable :
    ∀ i s, (φ n ε) i s → Module.indistinguishable (expM n ε) (mod n) i s := by
      intros i s Hφ
      constructor
      <;> dsimp [drcomponents, drunfold_defs] at *
      · intros ident i' v Hinp
        sorry
      · intros ident i' v Hout
        sorry

  theorem correct : (expM n ε) ⊑ (mod n) := by
    apply (
      Module.refines_φ_refines
        (ϕ_indistinguishable n ε)
        (refines_initial n ε)
        (refines_φ n ε)
    )

end Graphiti.Noc
