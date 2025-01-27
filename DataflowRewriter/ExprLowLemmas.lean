/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.Module
import DataflowRewriter.ExprLow
import Mathlib.Tactic
import Mathlib.Logic.Function.Basic

open Batteries (AssocList)

namespace DataflowRewriter

def Module.toBaseExprLow {Ident S} (m : Module Ident S) (inst typ : Ident) : ExprLow Ident :=
  .base (m.toPortMapping inst) typ

namespace ExprLow

-- theorem invertibleMap {α} [DecidableEq α] {p : Batteries.AssocList α α} {a b} :
--   invertible p →
--   (p.append p.inverse).find? a = some b → (p.append p.inverse).find? b = some a := by

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

theorem filterId_empty {α} [DecidableEq α] : PortMapping.filterId (Ident := α) ∅ = ∅ := by rfl

@[drunfold] def build_module'
    : (e : ExprLow Ident) → Option (Σ T, Module Ident T)
| .base i e => do
  let mod ← ε.find? e
  return ⟨ _, mod.2.renamePorts i ⟩
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

/- For now we will ensure this structurally by filtering out keys that are not in the base module. -/
def wf_mapping : ExprLow Ident → Bool
| .base inst typ =>
  match ε.find? typ with
  | .some mod =>
    inst.input.keysList.Perm mod.2.inputs.keysList
    ∧ inst.output.keysList.Perm mod.2.outputs.keysList
    ∧ inst.input.keysList.Nodup
    ∧ inst.output.keysList.Nodup
  | .none => false
| .product e₁ e₂ => e₁.wf_mapping ∧ e₂.wf_mapping
| .connect o i e => e.wf_mapping

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

-- theorem wf_modify_expression {e : ExprLow Ident} {i i'}:
--   (ε.find? i').isSome →
--   e.wf ε →
--   (e.modify i i').wf ε := by

theorem build_base_in_env {T inst i mod} :
  ε.find? i = some ⟨ T, mod ⟩ →
  build_module' ε (base inst i) = some ⟨ T, mod.renamePorts inst ⟩ := by
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
  build_module ε (.base r i) = ⟨ m.fst, m.snd.renamePorts r ⟩ := by
  intro h; simp only [drunfold]; rw [h]; simp

theorem build_module_unfold_2 {r i} :
  ε.find? i = none →
  build_module' ε (.base r i) = none := by
  intro h; simp only [drunfold]; rw [h]; simp

theorem build_module_type_rename' {e : ExprLow Ident} {f g} :
  (e.mapPorts2 f g |>.build_module' ε).isSome = (e.build_module' ε).isSome := by
  induction e with
  | base map typ =>
    simp [drunfold, -AssocList.find?_eq]
    cases (AssocList.find? typ ε) <;> simp
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

def _root_.Sigma.map2 {α t} (pair : @Sigma α t) (f : ∀ {a}, t a → t a) : Sigma t := ⟨ _, f pair.snd ⟩

theorem mapKey_comm {α} {m : PortMap Ident α} {inst f}:
  /- Pretty sure these are true based on wf_mapping. -/
  m.mapKey (Module.bijectivePortRenaming (inst.mapVal (fun x => f))) =
      (m.mapKey (Module.bijectivePortRenaming inst)).mapKey f := by sorry

theorem eraseAll_comm_inputs {S f g i} {m : Module Ident S}:
  AssocList.eraseAll (f i) (m.mapPorts2 f g).inputs = AssocList.mapKey f (AssocList.eraseAll i m.inputs) := by
  obtain ⟨min, mout, mint⟩ := m
  unfold Module.mapPorts2 Module.mapInputPorts Module.mapOutputPorts
  exact AssocList.eraseAll_comm_mapKey

theorem eraseAll_comm_outputs {S f g i} {m : Module Ident S}:
  AssocList.eraseAll (g i) (m.mapPorts2 f g).outputs = AssocList.mapKey g (AssocList.eraseAll i m.outputs) := by
  obtain ⟨min, mout, mint⟩ := m
  unfold Module.mapPorts2 Module.mapInputPorts Module.mapOutputPorts
  exact AssocList.eraseAll_comm_mapKey

theorem find?_comm_inputs {S f g i} {m : Module Ident S} (inj : Function.Injective f) :
  (AssocList.find? (f i) (m.mapPorts2 f g).inputs) = (AssocList.find? i m.inputs) := by
  obtain ⟨min, mout, mint⟩ := m
  unfold Module.mapPorts2 Module.mapInputPorts Module.mapOutputPorts
  exact AssocList.mapKey_find? inj

theorem find?_comm_outputs {S f g i} {m : Module Ident S} (inj : Function.Injective g):
  (AssocList.find? (g i) (m.mapPorts2 f g).outputs) = (AssocList.find? i m.outputs) := by
  obtain ⟨min, mout, mint⟩ := m
  unfold Module.mapPorts2 Module.mapInputPorts Module.mapOutputPorts
  exact AssocList.mapKey_find? inj

omit [DecidableEq Ident] in
theorem mapPorts2_mapKey_inputs {S} {f g} {m : Module Ident S} :
  (m.mapPorts2 f g).inputs = m.inputs.mapKey f := rfl

omit [DecidableEq Ident] in
theorem mapPorts2_mapKey_outputs {S} {f g} {m : Module Ident S} :
  (m.mapPorts2 f g).outputs = m.outputs.mapKey g := rfl

theorem rename_build_module_eq {e : ExprLow Ident} {f g} (h : Function.Bijective f) (h' : Function.Bijective g) :
  e.wf_mapping ε →
  ((e.mapPorts2 f g).build_module' ε) = ((e.build_module' ε).map (·.map id (fun _ y => y.mapPorts2 f g))) := by
  induction e with
  | base map typ =>
    intro hwf_mapping
    cases hfind : (AssocList.find? typ ε).isSome
    · simp [-AssocList.find?_eq] at hfind
      rw [build_module_unfold_2 hfind]
      dsimp [drunfold]; rw [hfind]; rfl
    · rw [Option.isSome_iff_exists] at hfind; obtain ⟨m, hfind⟩ := hfind
      rw [build_base_in_env hfind]
      dsimp [drunfold]; rw [hfind]; dsimp
      obtain ⟨mT, me⟩ := m
      obtain ⟨min, mout, mint⟩ := me; dsimp
      congr
      -- unfold PortMapping.filterId; dsimp
      unfold Module.renamePorts
      dsimp
      unfold Module.mapPorts2
      unfold Module.mapInputPorts Module.mapOutputPorts; dsimp
      congr 1
      · rw [mapKey_comm]
      . rw [mapKey_comm]
  | connect o i e ih =>
    intro hwf_mapping
    dsimp [wf_mapping] at hwf_mapping; specialize ih hwf_mapping
    dsimp [drunfold]
    cases hfind : build_module' ε (mapPorts2 f g e)
    · unfold mapPorts2 at hfind ih; rw [hfind]; dsimp
      rw [hfind] at ih; symm at ih; rw [Option.map_eq_none'] at ih; rw [ih]; rfl
    · unfold mapPorts2 at hfind ih; rw [hfind] at ih ⊢; dsimp
      symm at ih; rw [Option.map_eq_some'] at ih; obtain ⟨m, hbuild1, hbuild2⟩ := ih
      rw [hbuild1]; dsimp [Sigma.map];
      unfold Sigma.map at hbuild2; rename_i val; cases val; cases m; dsimp at *
      cases hbuild2; congr 3
      · rw [eraseAll_comm_inputs]
      · rw [eraseAll_comm_outputs]
      · rw [find?_comm_outputs h'.injective, find?_comm_inputs h.injective]; rfl
  | product e₁ e₂ ih₁ ih₂ =>
    intro hwf_mapping
    dsimp [wf_mapping] at hwf_mapping; simp at hwf_mapping
    specialize ih₁ hwf_mapping.1
    specialize ih₂ hwf_mapping.2
    dsimp [drunfold]
    cases hfind : build_module' ε (mapPorts2 f g e₁) <;> cases hfind₂ : build_module' ε (mapPorts2 f g e₂)
    · unfold mapPorts2 at hfind ih₁ ih₂ hfind₂; rw [hfind,hfind₂]; dsimp
      rw [hfind] at ih₁; rw [hfind₂] at ih₂; symm at ih₁ ih₂; rw [Option.map_eq_none'] at ih₁ ih₂; rw [ih₁,ih₂]; rfl
    · unfold mapPorts2 at hfind ih₁ ih₂ hfind₂; rw [hfind,hfind₂]; dsimp
      rw [hfind] at ih₁; rw [hfind₂] at ih₂; symm at ih₁ ih₂; rw [Option.map_eq_none'] at ih₁; rw [ih₁]; rfl
    · unfold mapPorts2 at hfind ih₁ ih₂ hfind₂; rw [hfind,hfind₂]; dsimp
      rw [hfind] at ih₁; rw [hfind₂] at ih₂; symm at ih₁ ih₂; rw [Option.map_eq_none'] at ih₂; rw [ih₂]
      rw [Option.map_eq_some'] at ih₁; obtain ⟨a, h1, h2⟩ := ih₁
      rw [h1]; rfl
    · unfold mapPorts2 at hfind ih₁ ih₂ hfind₂; rw [hfind,hfind₂]; dsimp
      rw [hfind] at ih₁; rw [hfind₂] at ih₂; symm at ih₁ ih₂;
      rw [Option.map_eq_some'] at ih₁ ih₂
      obtain ⟨m₁, ih1₁, ih2₁⟩ := ih₁
      obtain ⟨m₂, ih1₂, ih2₂⟩ := ih₂
      rw [ih1₂,ih1₁]; dsimp
      unfold Sigma.map at ih2₁ ih2₂ ⊢; dsimp at *
      rename_i val val1; cases val; cases val1
      cases ih2₁; cases ih2₂
      dsimp; congr 3
      · simp [mapPorts2_mapKey_inputs,AssocList.mapVal_mapKey,AssocList.mapVal_mapKey,AssocList.mapKey_append]
      · simp [mapPorts2_mapKey_outputs,AssocList.mapVal_mapKey,AssocList.mapVal_mapKey,AssocList.mapKey_append]

theorem rename_build_module_heq {e : ExprLow Ident} {f g} (h : Function.Bijective f) (h' : Function.Bijective g) :
  HEq ([e| e.mapPorts2 f g, ε]) ([e| e, ε ].mapPorts2 f g) := by
  induction e with
  | base map typ =>
    cases hfind : (AssocList.find? typ ε).isSome
    · simp [-AssocList.find?_eq] at hfind
      unfold build_module_expr build_module
      rw [build_module_unfold_2 hfind]
      dsimp [drunfold]; rw [hfind]; dsimp; constructor
    · rw [Option.isSome_iff_exists] at hfind; obtain ⟨m, hfind⟩ := hfind
      unfold build_module_expr build_module
      rw [build_base_in_env hfind]
      dsimp [drunfold]; rw [hfind]; dsimp
      obtain ⟨mT, me⟩ := m
      obtain ⟨min, mout, mint⟩ := me; dsimp
      congr
      -- unfold PortMapping.filterId; dsimp
      unfold Module.renamePorts
      dsimp
      unfold Module.mapPorts2
      unfold Module.mapInputPorts Module.mapOutputPorts; dsimp
      congr 1
      · sorry
      . sorry
  | connect o i e ih =>
    dsimp [drunfold]
    cases hfind : (build_module' ε e)
    all_goals sorry
  | _ => sorry

theorem rename_build_module1 {e f g} :
  Function.Bijective f → Function.Bijective g →
  ([e| e, ε ]).mapPorts2 f g ⊑ ([e| e.mapPorts2 f g, ε]) := by sorry

theorem rename_build_module2 {e f g} :
  Function.Bijective f → Function.Bijective g →
  ([e| e.mapPorts2 f g, ε]) ⊑ ([e| e, ε ]).mapPorts2 f g := by sorry

section Refinement

universe v w

variable {Ident : Type w}
variable [DecidableEq Ident]

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
  replace wf1 := wf_builds_module wf1
  replace wf2 := wf_builds_module wf2
  replace wf3 := wf_builds_module wf3
  replace wf4 := wf_builds_module wf4
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
  replace wf1 := wf_builds_module wf1
  replace wf2 := wf_builds_module wf2
  simp only [Option.isSome_iff_exists] at *
  rcases wf1 with ⟨ m₁, wf1 ⟩
  rcases wf2 with ⟨ m₂, wf2 ⟩
  simp only [build_module_expr, build_module, build_module'] at *
  rw [wf1,wf2] at ref ⊢
  solve_by_elim [Module.refines_connect]

-- theorem substition' {I I' i i' mod mod' iexpr} :
--     iexpr.wf ε →
--     ε.find? i = some ⟨ I, mod ⟩ →
--     ε.find? i' = some ⟨ I', mod' ⟩ →
--     mod ⊑ mod' →
--     [e| iexpr, ε ] ⊑ ([e| iexpr.modify i i', ε ]) := by
--   unfold build_module_expr
--   induction iexpr generalizing i i' mod mod' with
--   | base inst typ =>
--     intro hwf hfind₁ hfind₂ Href
--     dsimp [drunfold]
--     by_cases h : typ = i
--     · subst typ
--       rw [hfind₁]; dsimp [drunfold]
--       have : (if i = i then ExprLow.base inst i' else .base inst i) = .base inst i' := by
--         simp only [↓reduceIte]
--       rw [this, build_base_in_env hfind₂]; simp
--       solve_by_elim [Module.refines_renamePorts]
--     · have : (if typ = i then ExprLow.base inst i' else .base inst typ) = .base inst typ := by
--         simp only [↓reduceIte, h]
--       rw [this]; simp [drunfold,Module.refines_reflexive]
--   | product e₁ e₂ ihe₁ ihe₂ =>
--     intro hwf hf₁ hf₂ href
--     have e₁wf : e₁.wf ε := by simp [all, wf] at hwf ⊢; simp [hwf]
--     have e₂wf : e₂.wf ε := by simp [all, wf] at hwf ⊢; simp [hwf]
--     have some_isSome : (ε.find? i').isSome := by simp only [*]; simp
--     apply refines_product <;> solve_by_elim [wf_modify_expression]
--   | connect o i e =>
--     intro hwf hfind₁ hfind₂ href
--     simp only [modify]
--     have e₁wf : e.wf ε := by simp [all, wf] at hwf ⊢; simp [hwf]
--     have some_isSome : (ε.find? i').isSome := by simp only [*]; simp
--     apply refines_connect <;> solve_by_elim [wf_modify_expression]

-- theorem substition {I I' i i' mod mod' iexpr} :
--     iexpr.wf ε →
--     ε.find? i = some ⟨ I, mod ⟩ →
--     ε.find? i' = some ⟨ I', mod' ⟩ →
--     mod' ⊑ mod →
--     [e| iexpr.modify i i', ε ] ⊑ ([e| iexpr, ε ]) := by
--   unfold build_module_expr
--   induction iexpr generalizing i i' mod mod' with
--   | base inst typ =>
--     intro hwf hfind₁ hfind₂ Href
--     dsimp [drunfold]
--     by_cases h : typ = i
--     · subst typ
--       rw [hfind₁]; dsimp [drunfold]
--       have : (if i = i then ExprLow.base inst i' else .base inst i) = .base inst i' := by
--         simp only [↓reduceIte]
--       rw [this, build_base_in_env hfind₂]; simp
--       solve_by_elim [Module.refines_renamePorts]
--     · have : (if typ = i then ExprLow.base inst i' else .base inst typ) = .base inst typ := by
--         simp only [↓reduceIte, h]
--       rw [this]; simp [drunfold,Module.refines_reflexive]
--   | product e₁ e₂ ihe₁ ihe₂ =>
--     intro hwf hf₁ hf₂ href
--     have e₁wf : e₁.wf ε := by simp [all, wf] at hwf ⊢; simp [hwf]
--     have e₂wf : e₂.wf ε := by simp [all, wf] at hwf ⊢; simp [hwf]
--     have some_isSome : (ε.find? i').isSome := by simp only [*]; simp
--     apply refines_product <;> solve_by_elim [wf_modify_expression]
--   | connect o i e =>
--     intro hwf hfind₁ hfind₂ href
--     simp only [modify]
--     have e₁wf : e.wf ε := by simp [all, wf] at hwf ⊢; simp [hwf]
--     have some_isSome : (ε.find? i').isSome := by simp only [*]; simp
--     apply refines_connect <;> solve_by_elim [wf_modify_expression]

attribute [-drunfold] check_eq

theorem check_eq_symm {iexpr iexpr' : ExprLow Ident} :
  iexpr.check_eq iexpr' → iexpr'.check_eq iexpr := by
  induction iexpr generalizing iexpr' <;> unfold check_eq <;> cases iexpr' <;> intro heq
  any_goals contradiction
  · simp_all; and_intros <;> (apply AssocList.EqExt.symm; simp only [*])
  · aesop
  · aesop

theorem check_eq_wf {iexpr iexpr' : ExprLow Ident} :
  iexpr.check_eq iexpr' →
  iexpr.wf ε → iexpr'.wf ε := by sorry

theorem check_eq_refines {iexpr iexpr'} :
  iexpr.check_eq iexpr' → iexpr.wf ε →
  [e| iexpr, ε ] ⊑ ([e| iexpr', ε ]) := by
  revert iexpr'
  induction iexpr with
  | base inst typ =>
    intro iexpr' heq hwf
    cases iexpr' <;> try contradiction
    rename_i map' typ'
    unfold check_eq at heq; simp at heq
    obtain ⟨typeq, heq1, heq2, hnodup1, hnodup2, hnodup3, hnodup4⟩ := heq
    dsimp [drunfold]
    subst typ'
    cases h: (AssocList.find? typ ε) with
    | none =>
      apply Module.refines_reflexive
    | some mod =>
      dsimp; rw (occs := .pos [2]) [Module.renamePorts_EqExt (p' := inst)]
      apply Module.refines_reflexive
      any_goals (unfold PortMapping.wf; solve_by_elim)
      cases map'; cases inst; solve_by_elim
  | product e₁ e₂ ih₁ ih₂ =>
    intro iexpr' heq hwf
    have hwf' := check_eq_wf _ ‹_› ‹_›
    cases iexpr' <;> try contradiction
    rename_i e₁' e₂'
    apply refines_product
    any_goals (unfold wf all at hwf hwf'; unfold wf; aesop)
    apply ih₁; dsimp [check_eq] at heq; aesop
    unfold wf all at hwf hwf'; unfold wf; aesop
    apply ih₂; dsimp [check_eq] at heq; aesop
    unfold wf all at hwf hwf'; unfold wf; aesop
  | connect o i e ih =>
    intro iexpr' heq hwf
    have hwf' := check_eq_wf _ ‹_› ‹_›
    cases iexpr' <;> try contradiction
    rename_i o' i' e'
    dsimp [check_eq] at heq; simp at heq
    repeat cases ‹_ ∧ _›; subst_vars
    apply refines_connect
    any_goals (unfold wf all at hwf hwf'; unfold wf; solve_by_elim)
    solve_by_elim

theorem abstract_refines {iexpr expr_pat i} :
    ε.find? i = some ⟨ _, [e| expr_pat, ε ] ⟩ →
    iexpr.wf ε →
    [e| iexpr, ε ] ⊑ ([e| iexpr.abstract expr_pat ∅ i, ε ]) := by
  unfold build_module_expr; intro hfind;
  induction iexpr with
  | base inst typ =>
    intro hwf
    dsimp [drunfold, Option.bind, Option.getD] at *
    by_cases h : (ExprLow.base inst typ).check_eq expr_pat
    · rw [h];
      dsimp
      simp [drunfold, Option.bind]
      rw [hfind]; simp
      have : ∃ m, Batteries.AssocList.find? typ ε = some m := by
        simp only [wf, all] at hwf
        simp only [←Option.isSome_iff_exists, Batteries.AssocList.contains_some, hwf]
      let ⟨ m, hb ⟩ := this; clear this; rw [hb]; simp
      cases expr_pat <;> simp [check_eq] at h
      let ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h; clear h
      subst_vars
      dsimp [drunfold, Option.bind] at *
      rw [hb] at hfind ⊢; simp [-AssocList.find?_eq] at *
      rw [Module.renamePorts_empty]
      rename_i m _; cases m
      rw (occs := .pos [2]) [Module.renamePorts_EqExt (p' := inst)]
      · apply Module.refines_reflexive
      · unfold PortMapping.wf AssocList.wf; simp only [*, and_self]
      · unfold PortMapping.wf AssocList.wf; simp only [*, and_self]
      · cases inst; constructor <;> simp only [*]
    · have : (if (base inst typ).check_eq expr_pat = true then base ∅ i else base inst typ) = base inst typ := by
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
    by_cases h : (e₁.product e₂).check_eq expr_pat
    · subst_vars
      simp only [wf,all,Bool.and_eq_true] at hwf; obtain ⟨hwf1, hwf2⟩ := hwf
      specialize ihe₁ hwf1; specialize ihe₂ hwf2
      rw [h]; dsimp; rw [build_module_unfold_1 hfind]; dsimp
      apply Module.refines_transitive (imod' := (build_module ε expr_pat).snd)
      · apply check_eq_refines; assumption; unfold wf all; aesop
      · rw [Module.renamePorts_empty]; apply Module.refines_reflexive
    · unfold abstract at ihe₁ ihe₂
      have : wf ε (e₁.replace expr_pat (base ∅ i)) := by
        apply wf_abstract; simp_all [wf, all]
        apply Batteries.AssocList.contains_some3; assumption
      have : wf ε (e₂.replace expr_pat (base ∅ i)) := by
        apply wf_abstract; simp_all [wf, all]
        apply Batteries.AssocList.contains_some3; assumption
      have : wf ε e₁ := by simp_all [wf, all]
      have : wf ε e₂ := by simp_all [wf, all]
      simp at h; rw [h]; dsimp
      apply refines_product <;> (try assumption)
      <;> [apply ihe₁ ; apply ihe₂] <;> simp_all [wf, all]
  | connect x y e ih =>
    simp [abstract, replace]
    intro hwf
    by_cases h : (connect x y e).check_eq expr_pat
    · subst_vars
      simp only [wf,all,Bool.and_eq_true] at hwf
      specialize ih hwf
      rw [h]; dsimp; rw [build_module_unfold_1 hfind]; dsimp
      apply Module.refines_transitive (imod' := (build_module ε expr_pat).snd)
      · apply check_eq_refines; assumption; unfold wf all; aesop
      · rw [Module.renamePorts_empty]; apply Module.refines_reflexive
    · have : wf ε (connect x y (e.replace expr_pat (base ∅ i))) := by
        simp [wf, all]
        convert_to wf ε (e.replace expr_pat (base ∅ i));
        simp [wf, all]
        apply wf_replace; assumption; simp only [wf, all]
        skip; apply Batteries.AssocList.contains_some2; rw [hfind]; rfl
      simp at h; rw [h]; solve_by_elim [refines_connect]

theorem abstract_refines2 {iexpr expr_pat i} :
    ε.find? i = some ⟨ _, [e| expr_pat, ε ] ⟩ →
    iexpr.wf ε →
    [e| iexpr.abstract expr_pat ∅ i, ε ] ⊑ ([e| iexpr, ε ]) := by
  unfold build_module_expr; intro hfind;
  induction iexpr with
  | base inst typ =>
    intro hwf
    dsimp [drunfold, Option.bind, Option.getD] at *
    by_cases h : (ExprLow.base inst typ).check_eq expr_pat
    · rw [h];
      dsimp
      simp [drunfold, Option.bind]
      rw [hfind]; simp
      have : ∃ m, Batteries.AssocList.find? typ ε = some m := by
        simp only [wf, all] at hwf
        simp only [←Option.isSome_iff_exists, Batteries.AssocList.contains_some, hwf]
      let ⟨ m, hb ⟩ := this; clear this; rw [hb]; simp
      cases expr_pat <;> simp [check_eq] at h
      let ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h; clear h
      subst_vars
      dsimp [drunfold, Option.bind] at *
      rw [hb] at hfind ⊢; simp [-AssocList.find?_eq] at *
      rw [Module.renamePorts_empty]
      rename_i m _; cases m
      rw (occs := .pos [1]) [Module.renamePorts_EqExt (p' := inst)]
      · apply Module.refines_reflexive
      · unfold PortMapping.wf AssocList.wf; simp only [*, and_self]
      · unfold PortMapping.wf AssocList.wf; simp only [*, and_self]
      · cases inst; constructor <;> simp only [*]
    · have : (if (base inst typ).check_eq expr_pat = true then base ∅ i else base inst typ) = base inst typ := by
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
    by_cases h : (e₁.product e₂).check_eq expr_pat
    · subst_vars
      simp only [wf,all,Bool.and_eq_true] at hwf; obtain ⟨hwf1, hwf2⟩ := hwf
      specialize ihe₁ hwf1; specialize ihe₂ hwf2
      rw [h]; dsimp; rw [build_module_unfold_1 hfind]; dsimp
      apply Module.refines_transitive (imod' := (build_module ε expr_pat).snd)
      · rw [Module.renamePorts_empty]; apply Module.refines_reflexive
      · apply check_eq_refines; apply check_eq_symm; assumption
        apply check_eq_wf; assumption; unfold wf all; aesop
    · unfold abstract at ihe₁ ihe₂
      have : wf ε (e₁.replace expr_pat (base ∅ i)) := by
        apply wf_abstract; simp_all [wf, all]
        apply Batteries.AssocList.contains_some3; assumption
      have : wf ε (e₂.replace expr_pat (base ∅ i)) := by
        apply wf_abstract; simp_all [wf, all]
        apply Batteries.AssocList.contains_some3; assumption
      have : wf ε e₁ := by simp_all [wf, all]
      have : wf ε e₂ := by simp_all [wf, all]
      simp at h; rw [h]; dsimp
      apply refines_product <;> (try assumption)
      <;> [apply ihe₁ ; apply ihe₂] <;> simp_all [wf, all]
  | connect x y e ih =>
    simp [abstract, replace]
    intro hwf
    by_cases h : (connect x y e).check_eq expr_pat
    · subst_vars
      simp only [wf,all,Bool.and_eq_true] at hwf
      specialize ih hwf
      rw [h]; dsimp; rw [build_module_unfold_1 hfind]; dsimp
      apply Module.refines_transitive (imod' := (build_module ε expr_pat).snd)
      · rw [Module.renamePorts_empty]; apply Module.refines_reflexive
      · apply check_eq_refines; apply check_eq_symm; assumption
        apply check_eq_wf; assumption; unfold wf all; aesop
    · have : wf ε (connect x y (e.replace expr_pat (base ∅ i))) := by
        simp [wf, all]
        convert_to wf ε (e.replace expr_pat (base ∅ i));
        simp [wf, all]
        apply wf_replace; assumption; simp only [wf, all]
        skip; apply Batteries.AssocList.contains_some2; rw [hfind]; rfl
      simp at h; rw [h]; solve_by_elim [refines_connect]

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
