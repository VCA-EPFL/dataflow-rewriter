/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.Module
import DataflowRewriter.ExprLow

open Batteries (AssocList)

namespace DataflowRewriter

def Module.toBaseExprLow {Ident S} (m : Module Ident S) (inst typ : Ident) : ExprLow Ident :=
  .base (m.toPortMapping inst) typ

namespace ExprLow

variable {Ident}
variable [DecidableEq Ident]

variable (ε : IdentMap Ident (Σ T : Type, Module Ident T))

@[drunfold] def get_types (i : Ident) : Type _ :=
  (ε.find? i) |>.map Sigma.fst |>.getD PUnit

@[drunfold] def ident_list : ExprLow Ident → List Ident
| .base i e => [e]
| .connect _ _ e => e.ident_list
| .product a b => a.ident_list ++ b.ident_list

abbrev EType ε (e : ExprLow Ident) := HVector (get_types ε) e.ident_list

@[drunfold] def build_moduleD
    : (e : ExprLow Ident) → Option (Module Ident (EType ε e))
| .base i e =>
  match h : ε.find? e with
  | some mod =>
    have H : mod.1 = get_types ε e := by
      simp [Batteries.AssocList.find?_eq] at h
      rcases h with ⟨ l, r ⟩
      simp_all [get_types]
    some ((H ▸ mod.2).liftD)
  | none => none
| .connect o i e' => do
  let e ← e'.build_moduleD
  return e.connect' o i
| .product a b => do
  let a ← a.build_moduleD;
  let b ← b.build_moduleD;
  return a.productD b

theorem build_moduleD.dep_rewrite {instIdent} : ∀ {modIdent : Ident} {ε a} (Hfind : ε.find? modIdent = a),
  (Option.rec (motive := fun x =>
    Batteries.AssocList.find? modIdent ε = x →
      Option (Module Ident (EType ε (base instIdent modIdent))))
    (fun h_1 => none)
    (fun val h_1 => some (build_moduleD.proof_2 ε modIdent val h_1 ▸ val.snd).liftD)
    (Batteries.AssocList.find? modIdent ε)
    (Eq.refl (Batteries.AssocList.find? modIdent ε))) =
  (Option.rec (motive := fun x => a = x → Option (Module Ident (EType ε (base instIdent modIdent))))
    (fun h_1 => none)
    (fun val h_1 => some (build_moduleD.proof_2 ε modIdent val (Hfind ▸ h_1) ▸ val.snd).liftD)
    a
    (Eq.refl a)) := by intro a b c d; cases d; rfl

theorem filterId_empty : filterId (Ident := Ident) ∅ = ∅ := by rfl

@[drunfold] def build_module'
    : (e : ExprLow Ident) → Option (Σ T, Module Ident T)
| .base i e => do
  let mod ← ε.find? e
  return ⟨ _, mod.2.renamePorts (filterId i) ⟩
| .connect o i e' => do
  let e ← e'.build_module'
  return ⟨ _, e.2.connect' o i ⟩
| .product a b => do
  let a ← a.build_module'
  let b ← b.build_module'
  return ⟨ _, a.2.product b.2 ⟩

inductive type_correct_module : ExprLow Ident → Prop where
| base : ∀ i e, type_correct_module (.base i e)
| connect : ∀ o i e e',
  type_correct_module e →
  e.build_module' ε = some e' →
  (e'.2.outputs.getIO o).1 = (e'.2.inputs.getIO i).1 →
  type_correct_module (.connect o i e)
| product : ∀ e₁ e₂,
  type_correct_module e₁ →
  type_correct_module e₂ →
  type_correct_module (.product e₁ e₂)

@[drunfold] def build_module_names
    : (e : ExprLow Ident) → List (PortMapping Ident × Ident)
| .base i e => [(i, e)]
| .connect o i e' => e'.build_module_names
| .product a b => a.build_module_names ++ b.build_module_names

@[drunfold] def build_moduleP
    (e : ExprLow Ident)
    (h : (build_module' ε e).isSome = true := by rfl)
    : Σ T, Module Ident T := e.build_module' ε |>.get h

@[drunfold] def build_module
    (e : ExprLow Ident)
    : Σ T, Module Ident T := e.build_module' ε |>.getD ⟨ Unit, Module.empty _ ⟩

@[drunfold] abbrev build_module_expr
    (e : ExprLow Ident)
    : Module Ident (e.build_module ε).1 := (e.build_module ε).2

@[drunfold] abbrev build_module_type
    (e : ExprLow Ident)
    : Type _ := (e.build_module ε).1

notation:25 "[e| " e ", " ε " ]" => build_module_expr ε e
notation:25 "[T| " e ", " ε " ]" => build_module_type ε e

def wf : ExprLow Ident → Bool := all (λ typ => ε.contains typ)

variable {ε}

theorem wf_builds_module {e} : wf ε e → (e.build_module' ε).isSome := by
  induction e with
  | base inst typ =>
    intro hwf; dsimp [wf, all] at hwf
    simp only [drunfold]
    have := Batteries.AssocList.contains_some hwf
    rw [Option.isSome_iff_exists] at this; cases this
    simp only [*]; rfl
  | connect i o e ih =>
    intro hwf; dsimp [wf, all] at hwf
    specialize ih hwf
    simp only [drunfold]; rw [Option.isSome_iff_exists] at ih; cases ih
    simp only [*]; rfl
  | product e₁ e₂ ihe₁ ihe₂ =>
    intro hwf; dsimp [wf, all] at hwf; rw [Bool.and_eq_true] at hwf; cases hwf; rename_i ha hb
    specialize ihe₁ ha; specialize ihe₂ hb
    simp only [drunfold]; rw [Option.isSome_iff_exists] at ihe₁ ihe₂
    cases ihe₁; cases ihe₂
    simp only [*]; rfl

theorem wf_modify_expression {e : ExprLow Ident} {i i'}:
  (ε.find? i').isSome →
  e.wf ε →
  (e.modify i i').wf ε := by sorry

theorem build_base_in_env {T inst i mod} :
  ε.find? i = some ⟨ T, mod ⟩ →
  build_module' ε (base inst i) = some ⟨ T, mod.renamePorts (filterId inst) ⟩ := by
  intro h; dsimp [drunfold]; rw [h]; rfl

theorem wf_replace {e e_pat e'} : wf ε e → wf ε e' → wf ε (e.replace e_pat e') := by
  intro h wfe'; revert h
  induction e <;> (intros; simp [replace]; split <;> (try solve_by_elim) <;> simp_all [wf, all])

theorem wf_abstract {e e_pat a b} : wf ε e → ε.contains b → wf ε (e.abstract e_pat a b) := by
  unfold abstract; intros wf1 hcont
  apply wf_replace; assumption
  simp only [wf, all]; assumption

theorem build_module_unfold_1 {m r i} :
  ε.find? i = some m →
  build_module ε (.base r i) = ⟨ m.fst, m.snd.renamePorts (filterId r) ⟩ := by
  intro h; simp only [drunfold]; rw [h]; simp

theorem build_module_type_rename' {e : ExprLow Ident} {f g} :
  (e.mapPorts2 f g |>.build_module' ε).isSome = (e.build_module' ε).isSome := by
  induction e with
  | base map typ =>
    simp [drunfold, -AssocList.find?_eq]
  | connect o i e ih =>
    dsimp [drunfold, -AssocList.find?_eq]
    cases h : build_module' ε e
    · rw [h] at ih; simp [mapPorts2] at ih; simp [ih]
    · rw [h] at ih; simp at ih; rw [Option.isSome_iff_exists] at ih; rcases ih with ⟨_, ih⟩
      unfold mapPorts2 at *; rw [ih]; rfl
  | product e₁ e₂ ihe₁ ihe₂ =>
    dsimp [drunfold]
    cases h : (build_module' ε e₁)
    · rw [h] at ihe₁; simp [mapPorts2] at ihe₁; simp [ihe₁]
    · cases h2 : (build_module' ε e₂)
      · rw [h2] at ihe₂; simp [mapPorts2] at ihe₂; simp [ihe₂]
      · rw [h] at ihe₁; simp at ihe₁; rw [Option.isSome_iff_exists] at ihe₁; rcases ihe₁ with ⟨_, ihe₁⟩
        unfold mapPorts2 at *; rw [ihe₁];
        rw [h2] at ihe₂; simp at ihe₂; rw [Option.isSome_iff_exists] at ihe₂; rcases ihe₂ with ⟨_, ihe₂⟩
        rw [ihe₂]; rfl

theorem build_module_type_rename {e f g} :
  ([T| e.mapPorts2 f g, ε]) = ([T| e, ε ]) := by
  induction e with
  | base map typ =>
    simp [drunfold, -AssocList.find?_eq]
    cases h : (AssocList.find? typ ε) <;> rfl
  | connect o i e ie =>
    simp [drunfold, -AssocList.find?_eq]
    cases h : build_module' ε e
    · have : (build_module' ε (mapOutputPorts g (mapInputPorts f e))) = none := by
        have := build_module_type_rename' (ε := ε) (e := e) (f := f) (g := g)
        rw [h] at this; simp_all [mapPorts2]
      rw [this]; rfl
    · have := build_module_type_rename' (ε := ε) (e := e) (f := f) (g := g)
      rw [h] at this; dsimp at this; rw [Option.isSome_iff_exists] at this
      rcases this with ⟨a, this⟩
      dsimp [mapPorts2] at this; rw [this]
      unfold build_module_type build_module at *
      unfold mapPorts2 at *
      rw [this] at ie; rw [h] at ie
      dsimp at ie; assumption
  | product e₁ e₂ he₁ he₂ =>
    simp [drunfold, -AssocList.find?_eq]
    cases h : build_module' ε e₁
    · have : (build_module' ε (mapOutputPorts g (mapInputPorts f e₁))) = none := by
        have := build_module_type_rename' (ε := ε) (e := e₁) (f := f) (g := g)
        rw [h] at this; simp_all [mapPorts2]
      rw [this]; rfl
    · have this := build_module_type_rename' (ε := ε) (e := e₁) (f := f) (g := g)
      have this2 := build_module_type_rename' (ε := ε) (e := e₂) (f := f) (g := g)
      rw [h] at this; dsimp at this; rw [Option.isSome_iff_exists] at this; rcases this with ⟨ a, this ⟩
      cases h' : build_module' ε e₂
      · have this3 : (build_module' ε (mapOutputPorts g (mapInputPorts f e₂))) = none := by
          rw [h'] at this2; simp_all [mapPorts2]
        rw [this3]; unfold mapPorts2 at *; rw [this]; rfl
      · rw [h'] at this2; dsimp at this2; rw [Option.isSome_iff_exists] at this2
        rcases this2 with ⟨a, this2⟩
        dsimp [mapPorts2] at this this2; rw [this]
        unfold build_module_type build_module at *
        unfold mapPorts2 at *
        dsimp; rw [this2]; dsimp
        rw [h,this] at he₁
        rw [h',this2] at he₂
        simp at *; congr

def cast_module {S T} (h : S = T): Module Ident S = Module Ident T := by
  cases h; rfl

theorem rename_build_module {e : ExprLow Ident} {f g} (h : Function.Bijective f) (h' : Function.Bijective g) :
  (([e| e.mapPorts2 f g, ε])) = ((cast_module build_module_type_rename).mpr ([e| e, ε ])).mapPorts2 f g := by
  -- induction e with
  -- | base map typ =>
  --   dsimp [drunfold]
  --   cases h : (AssocList.find? typ ε).isSome
  --   · simp [-AssocList.find?_eq] at h
  --     sorry
  --   · sorry
  -- | connect o i e ih =>
  --   dsimp [drunfold]
  sorry

theorem rename_build_module2 {e f g} :
  Function.Bijective f → Function.Bijective g →
  ([e| e, ε ]).mapPorts2 f g ⊑ ([e| e.mapPorts2 f g, ε]) := by sorry

theorem rename_build_module3 {e f g} :
  Function.Bijective f → Function.Bijective g →
  ([e| e.mapPorts2 f g, ε]) ⊑ ([e| e, ε ]).mapPorts2 f g := by sorry

section Refinement

universe v w

variable {Ident : Type w}
variable [DecidableEq Ident]
variable [Inhabited Ident]

variable (ε : IdentMap Ident ((T : Type _) × Module Ident T))

variable {S : Type v}
variable (smod : Module Ident S)

theorem refines_product {e₁ e₂ e₁' e₂'} :
    wf ε e₁ → wf ε e₂ → wf ε e₁' → wf ε e₂' →
    [e| e₁, ε ] ⊑ ([e| e₁', ε ]) →
    [e| e₂, ε ] ⊑ ([e| e₂', ε ]) →
    [e| e₁.product e₂, ε ] ⊑ ([e| e₁'.product e₂', ε ]) := by
  intro wf1 wf2 wf3 wf4 ref1 ref2
  simp only [drunfold] at *
  apply wf_builds_module at wf1
  apply wf_builds_module at wf2
  apply wf_builds_module at wf3
  apply wf_builds_module at wf4
  simp only [Option.isSome_iff_exists] at *
  rcases wf1 with ⟨ m₁, wf1 ⟩
  rcases wf2 with ⟨ m₂, wf2 ⟩
  rcases wf3 with ⟨ m₁', wf3 ⟩
  rcases wf4 with ⟨ m₂', wf4 ⟩
  rw [wf1, wf2, wf3, wf4]
  rw [wf1, wf3] at ref1
  rw [wf2, wf4] at ref2
  solve_by_elim [Module.refines_product]

theorem refines_connect {e e' o i} :
    wf ε e → wf ε e' →
    [e| e, ε ] ⊑ ([e| e', ε ]) →
    [e| e.connect o i, ε ] ⊑ ([e| e'.connect o i, ε ]) := by
  intro wf1 wf2 ref
  apply wf_builds_module at wf1
  apply wf_builds_module at wf2
  simp only [Option.isSome_iff_exists] at *
  rcases wf1 with ⟨ m₁, wf1 ⟩
  rcases wf2 with ⟨ m₂, wf2 ⟩
  simp only [build_module_expr, build_module, build_module'] at *
  rw [wf1,wf2] at ref ⊢
  solve_by_elim [Module.refines_connect]

theorem substition' {I I' i i' mod mod' iexpr} :
    iexpr.wf ε →
    ε.find? i = some ⟨ I, mod ⟩ →
    ε.find? i' = some ⟨ I', mod' ⟩ →
    mod ⊑ mod' →
    [e| iexpr, ε ] ⊑ ([e| iexpr.modify i i', ε ]) := by
  unfold build_module_expr
  induction iexpr generalizing i i' mod mod' with
  | base inst typ =>
    intro hwf hfind₁ hfind₂ Href
    dsimp [drunfold]
    by_cases h : typ = i
    · subst typ
      rw [hfind₁]; dsimp [drunfold]
      have : (if i = i then ExprLow.base inst i' else .base inst i) = .base inst i' := by
        simp only [↓reduceIte]
      rw [this, build_base_in_env hfind₂]; simp
      solve_by_elim [Module.refines_renamePorts]
    · have : (if typ = i then ExprLow.base inst i' else .base inst typ) = .base inst typ := by
        simp only [↓reduceIte, h]
      rw [this]; simp [drunfold,Module.refines_reflexive]
  | product e₁ e₂ ihe₁ ihe₂ =>
    intro hwf hf₁ hf₂ href
    have e₁wf : e₁.wf ε := by simp [all, wf] at hwf ⊢; simp [hwf]
    have e₂wf : e₂.wf ε := by simp [all, wf] at hwf ⊢; simp [hwf]
    have some_isSome : (ε.find? i').isSome := by simp only [*]; simp
    apply refines_product <;> solve_by_elim [wf_modify_expression]
  | connect o i e =>
    intro hwf hfind₁ hfind₂ href
    simp only [modify]
    have e₁wf : e.wf ε := by simp [all, wf] at hwf ⊢; simp [hwf]
    have some_isSome : (ε.find? i').isSome := by simp only [*]; simp
    apply refines_connect <;> solve_by_elim [wf_modify_expression]

theorem substition {I I' i i' mod mod' iexpr} :
    iexpr.wf ε →
    ε.find? i = some ⟨ I, mod ⟩ →
    ε.find? i' = some ⟨ I', mod' ⟩ →
    mod' ⊑ mod →
    [e| iexpr.modify i i', ε ] ⊑ ([e| iexpr, ε ]) := by
  unfold build_module_expr
  induction iexpr generalizing i i' mod mod' with
  | base inst typ =>
    intro hwf hfind₁ hfind₂ Href
    dsimp [drunfold]
    by_cases h : typ = i
    · subst typ
      rw [hfind₁]; dsimp [drunfold]
      have : (if i = i then ExprLow.base inst i' else .base inst i) = .base inst i' := by
        simp only [↓reduceIte]
      rw [this, build_base_in_env hfind₂]; simp
      solve_by_elim [Module.refines_renamePorts]
    · have : (if typ = i then ExprLow.base inst i' else .base inst typ) = .base inst typ := by
        simp only [↓reduceIte, h]
      rw [this]; simp [drunfold,Module.refines_reflexive]
  | product e₁ e₂ ihe₁ ihe₂ =>
    intro hwf hf₁ hf₂ href
    have e₁wf : e₁.wf ε := by simp [all, wf] at hwf ⊢; simp [hwf]
    have e₂wf : e₂.wf ε := by simp [all, wf] at hwf ⊢; simp [hwf]
    have some_isSome : (ε.find? i').isSome := by simp only [*]; simp
    apply refines_product <;> solve_by_elim [wf_modify_expression]
  | connect o i e =>
    intro hwf hfind₁ hfind₂ href
    simp only [modify]
    have e₁wf : e.wf ε := by simp [all, wf] at hwf ⊢; simp [hwf]
    have some_isSome : (ε.find? i').isSome := by simp only [*]; simp
    apply refines_connect <;> solve_by_elim [wf_modify_expression]

theorem abstract_refines {iexpr expr_pat i} :
    ε.find? i = some ⟨ _, [e| expr_pat, ε ] ⟩ →
    iexpr.wf ε →
    [e| iexpr, ε ] ⊑ ([e| iexpr.abstract expr_pat ∅ i, ε ]) := by
  unfold build_module_expr; intro hfind;
  induction iexpr with
  | base inst typ =>
    intro hwf
    dsimp [drunfold, Option.bind, Option.getD] at *
    by_cases h : .base inst typ = expr_pat
    · rw [h];
      have : (if expr_pat = expr_pat then .base ∅ i else expr_pat) = .base ∅ i := by simp
      rw [this]; clear this; simp [drunfold, Option.bind]
      rw [hfind]; simp
      have : ∃ m, Batteries.AssocList.find? typ ε = some m := by
        simp only [wf, all] at hwf
        simp only [←Option.isSome_iff_exists, Batteries.AssocList.contains_some, hwf]
      rcases this with ⟨ m, hb ⟩; rw [hb]; simp
      subst_vars
      simp [drunfold, Option.bind, Option.getD, hb]
      rw [hb]; simp
      rw [filterId_empty,Module.renamePorts_empty]; apply Module.refines_reflexive
    · have : (if base inst typ = expr_pat then base ∅ i else base inst typ) = base inst typ := by
        simp [h]
      rw [this]; clear this
      have : ∃ m, Batteries.AssocList.find? typ ε = some m := by
        simp only [wf, all] at hwf
        simp only [←Option.isSome_iff_exists, Batteries.AssocList.contains_some, hwf]
      cases this; rename_i a ha
      dsimp [drunfold]; rw [ha]; simp [Module.refines_reflexive]
  | product e₁ e₂ ihe₁ ihe₂ =>
    simp [abstract, replace]
    intro hwf
    generalize H : (if e₁.product e₂ = expr_pat then base ∅ i
        else (e₁.replace expr_pat (base ∅ i)).product (e₂.replace expr_pat (base ∅ i))) = y
    split at H <;> subst y <;> rename_i h
    · subst_vars
      rw [build_module_unfold_1 hfind, filterId_empty, Module.renamePorts_empty]
      apply Module.refines_reflexive
    · unfold abstract at ihe₁ ihe₂
      have : wf ε (e₁.replace expr_pat (base ∅ i)) := by
        apply wf_abstract; simp_all [wf, all]
        apply Batteries.AssocList.contains_some3; assumption
      have : wf ε (e₂.replace expr_pat (base ∅ i)) := by
        apply wf_abstract; simp_all [wf, all]
        apply Batteries.AssocList.contains_some3; assumption
      have : wf ε e₁ := by simp_all [wf, all]
      have : wf ε e₂ := by simp_all [wf, all]
      apply refines_product <;> (try assumption)
      <;> [apply ihe₁ ; apply ihe₂] <;> simp_all [wf, all]
  | connect x y e ih =>
    simp [abstract, replace]
    intro hwf
    generalize h : (if connect x y e = expr_pat then base ∅ i else connect x y (e.replace expr_pat (base ∅ i))) = y
    split at h <;> subst_vars
    · rw [build_module_unfold_1 hfind, filterId_empty, Module.renamePorts_empty]
      apply Module.refines_reflexive
    · have : wf ε (connect x y (e.replace expr_pat (base ∅ i))) := by
        simp [wf, all]
        convert_to wf ε (e.replace expr_pat (base ∅ i));
        simp [wf, all]
        apply wf_replace; assumption; simp only [wf, all]
        skip; apply Batteries.AssocList.contains_some2; rw [hfind]; rfl
      solve_by_elim [refines_connect]

theorem abstract_refines2 {iexpr expr_pat i} :
    ε.find? i = some ⟨ _, [e| expr_pat, ε ] ⟩ →
    iexpr.wf ε →
    [e| iexpr.abstract expr_pat ∅ i, ε ] ⊑ ([e| iexpr, ε ]) := by
  unfold build_module_expr; intro hfind;
  induction iexpr with
  | base inst typ =>
    intro hwf
    dsimp [drunfold, Option.bind, Option.getD] at *
    by_cases h : .base inst typ = expr_pat
    · rw [h];
      have : (if expr_pat = expr_pat then .base ∅ i else expr_pat) = .base ∅ i := by simp
      rw [this]; clear this; simp [drunfold, Option.bind]
      rw [hfind]; simp
      have : ∃ m, Batteries.AssocList.find? typ ε = some m := by
        simp only [wf, all] at hwf
        simp only [←Option.isSome_iff_exists, Batteries.AssocList.contains_some, hwf]
      rcases this with ⟨ m, hb ⟩; rw [hb]; simp
      subst_vars
      simp [drunfold, Option.bind, Option.getD, hb]
      rw [hb]; simp
      rw [filterId_empty, Module.renamePorts_empty]; apply Module.refines_reflexive
    · have : (if base inst typ = expr_pat then base ∅ i else base inst typ) = base inst typ := by
        simp [h]
      rw [this]; clear this
      have : ∃ m, Batteries.AssocList.find? typ ε = some m := by
        simp only [wf, all] at hwf
        simp only [←Option.isSome_iff_exists, Batteries.AssocList.contains_some, hwf]
      cases this; rename_i a ha
      dsimp [drunfold]; rw [ha]; simp [Module.refines_reflexive]
  | product e₁ e₂ ihe₁ ihe₂ =>
    simp [abstract, replace]
    intro hwf
    generalize H : (if e₁.product e₂ = expr_pat then base ∅ i
        else (e₁.replace expr_pat (base ∅ i)).product (e₂.replace expr_pat (base ∅ i))) = y
    split at H <;> subst y <;> rename_i h
    · subst_vars
      rw [build_module_unfold_1 hfind, filterId_empty, Module.renamePorts_empty]
      apply Module.refines_reflexive
    · unfold abstract at ihe₁ ihe₂
      have : wf ε (e₁.replace expr_pat (base ∅ i)) := by
        apply wf_abstract; simp_all [wf, all]
        apply Batteries.AssocList.contains_some3; assumption
      have : wf ε (e₂.replace expr_pat (base ∅ i)) := by
        apply wf_abstract; simp_all [wf, all]
        apply Batteries.AssocList.contains_some3; assumption
      have : wf ε e₁ := by simp_all [wf, all]
      have : wf ε e₂ := by simp_all [wf, all]
      apply refines_product <;> (try assumption)
      <;> [apply ihe₁ ; apply ihe₂] <;> simp_all [wf, all]
  | connect x y e ih =>
    simp [abstract, replace]
    intro hwf
    generalize h : (if connect x y e = expr_pat then base ∅ i else connect x y (e.replace expr_pat (base ∅ i))) = y
    split at h <;> subst_vars
    · rw [build_module_unfold_1 hfind, filterId_empty, Module.renamePorts_empty]
      apply Module.refines_reflexive
    · have : wf ε (connect x y (e.replace expr_pat (base ∅ i))) := by
        simp [wf, all]
        convert_to wf ε (e.replace expr_pat (base ∅ i));
        simp [wf, all]
        apply wf_replace; assumption; simp only [wf, all]
        skip; apply Batteries.AssocList.contains_some2; rw [hfind]; rfl
      solve_by_elim [refines_connect]

theorem replacement {iexpr e_new e_pat} :
    iexpr.wf ε → e_new.wf ε → e_pat.wf ε →
    [e| e_new, ε ] ⊑ ([e| e_pat, ε ]) →
    [e| iexpr.replace e_pat e_new, ε ] ⊑ ([e| iexpr, ε ]) := by
  unfold build_module_expr
  induction iexpr with
  | base inst typ =>
    intro hwf₁ hwf₂ hwf₃ Href
    dsimp [drunfold]
    by_cases h : base inst typ = e_pat
    · subst e_pat
      have : (if base inst typ = base inst typ then e_new else base inst typ) = e_new := by
        simp only [↓reduceIte]
      rw [this]
      dsimp [wf, all] at hwf₁
      solve_by_elim [Module.refines_renamePorts]
    · have : (if base inst typ = e_pat then e_new else base inst typ) = .base inst typ := by
        simp only [↓reduceIte, h]
      rw [this]; simp [drunfold,Module.refines_reflexive]
  | product e₁ e₂ ihe₁ ihe₂ =>
    intro hwf hf₁ hf₂ href
    have e₁wf : e₁.wf ε := by simp [all, wf] at hwf ⊢; simp [hwf]
    have e₂wf : e₂.wf ε := by simp [all, wf] at hwf ⊢; simp [hwf]
    dsimp [replace]
    by_cases h : e₁.product e₂ = e_pat
    · subst e_pat
      have : (if e₁.product e₂ = e₁.product e₂ then e_new
        else (e₁.replace (e₁.product e₂) e_new).product (e₂.replace (e₁.product e₂) e_new)) = e_new := by
        simp only [↓reduceIte]
      rwa [this]
    · have : (if e₁.product e₂ = e_pat then e_new else (e₁.replace e_pat e_new).product (e₂.replace e_pat e_new))
        = (e₁.replace e_pat e_new).product (e₂.replace e_pat e_new) := by
        simp only [↓reduceIte,h]
      rw [this]; clear this
      apply refines_product <;> solve_by_elim [wf_modify_expression,wf_replace]
  | connect o i e =>
    intro hwf hfind₁ hfind₂ href
    dsimp only [replace]
    have e₁wf : e.wf ε := by simp [all, wf] at hwf ⊢; simp [hwf]
    by_cases h : connect o i e = e_pat
    · subst_vars
      have : (if connect o i e = connect o i e then e_new else connect o i (e.replace (connect o i e) e_new)) = e_new := by
        simp only [↓reduceIte]
      rwa [this]
    · have : (if connect o i e = e_pat then e_new else connect o i (e.replace e_pat e_new)) = connect o i (e.replace e_pat e_new) := by
        simp only [↓reduceIte,h]
      rw [this]
      apply refines_connect <;> solve_by_elim [wf_modify_expression,wf_replace]

end Refinement

end ExprLow
end DataflowRewriter
