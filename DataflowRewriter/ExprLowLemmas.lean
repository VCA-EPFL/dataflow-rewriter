/-
Copyright (c) 2024-2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.Module
import DataflowRewriter.ExprLow
import DataflowRewriter.Environment
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
| .connect _ e => e.ident_list
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
| .connect c e' => do
  let e ← e'.build_moduleD
  return e.connect' c.output c.input
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
| .connect c e' => do
  let e ← e'.build_module'
  return ⟨ _, e.2.connect' c.output c.input ⟩
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
  type_correct_module (.connect { output := o, input := i } e)
| product : ∀ e₁ e₂,
  type_correct_module e₁ →
  type_correct_module e₂ →
  type_correct_module (.product e₁ e₂)

@[drunfold] def build_module_names
    : (e : ExprLow Ident) → List (PortMapping Ident × Ident)
| .base i e => [(i, e)]
| .connect _ e' => e'.build_module_names
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

@[drunfold]
def locally_wf : ExprLow Ident → Bool := all' (λ f _ => f.input.invertible ∧ f.output.invertible)

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
| .connect _ e => e.wf_mapping

variable {ε}

theorem wf_builds_module {e} : wf ε e → (e.build_module' ε).isSome := by
  induction e with
  | base inst typ =>
    intro hwf; dsimp [wf, all] at hwf
    simp only [drunfold]
    have := Batteries.AssocList.contains_some hwf
    rw [Option.isSome_iff_exists] at this; cases this
    simp only [*]; rfl
  | connect _ e ih =>
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

axiom wf_modify_expression {e : ExprLow Ident} {i i'}:
  (ε.find? i').isSome →
  e.wf ε →
  (e.modify i i').wf ε

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

-- theorem build_module_type_rename' {e : ExprLow Ident} {f g} :
--   (e.mapPorts2 f g |>.build_module' ε).isSome = (e.build_module' ε).isSome := by
--   induction e with
--   | base map typ =>
--     simp [drunfold, -AssocList.find?_eq]
--     cases (AssocList.find? typ ε) <;> simp
--   | connect _ e ih =>
--     dsimp [drunfold, -AssocList.find?_eq]
--     cases h : build_module' ε e
--     · rw [h] at ih; simp [mapPorts2] at ih; simp [ih]
--     · rw [h] at ih; simp at ih; rw [Option.isSome_iff_exists] at ih; rcases ih with ⟨_, ih⟩
--       unfold mapPorts2 at *; rw [ih]; rfl
--   | product e₁ e₂ ihe₁ ihe₂ =>
--     dsimp [drunfold]
--     cases h : (build_module' ε e₁)
--     · rw [h] at ihe₁; simp [mapPorts2] at ihe₁; simp [ihe₁]
--     · cases h2 : (build_module' ε e₂)
--       · rw [h2] at ihe₂; simp [mapPorts2] at ihe₂; simp [ihe₂]
--       · rw [h] at ihe₁; simp at ihe₁; rw [Option.isSome_iff_exists] at ihe₁; rcases ihe₁ with ⟨_, ihe₁⟩
--         unfold mapPorts2 at *; rw [ihe₁];
--         rw [h2] at ihe₂; simp at ihe₂; rw [Option.isSome_iff_exists] at ihe₂; rcases ihe₂ with ⟨_, ihe₂⟩
--         rw [ihe₂]; rfl

-- theorem build_module_type_rename {e f g} :
--   ([T| e.mapPorts2 f g, ε]) = ([T| e, ε ]) := by
--   induction e with
--   | base map typ =>
--     simp [drunfold, -AssocList.find?_eq]
--     cases h : (AssocList.find? typ ε) <;> rfl
--   | connect _ e ie =>
--     simp [drunfold, -AssocList.find?_eq]
--     cases h : build_module' ε e
--     · have : (build_module' ε (mapOutputPorts g (mapInputPorts f e))) = none := by
--         have := build_module_type_rename' (ε := ε) (e := e) (f := f) (g := g)
--         rw [h] at this; simp_all [mapPorts2]
--       rw [this]; rfl
--     · have := build_module_type_rename' (ε := ε) (e := e) (f := f) (g := g)
--       rw [h] at this; dsimp at this; rw [Option.isSome_iff_exists] at this
--       rcases this with ⟨a, this⟩
--       dsimp [mapPorts2] at this; rw [this]
--       unfold build_module_type build_module at *
--       unfold mapPorts2 at *
--       rw [this] at ie; rw [h] at ie
--       dsimp at ie; assumption
--   | product e₁ e₂ he₁ he₂ =>
--     simp [drunfold, -AssocList.find?_eq]
--     cases h : build_module' ε e₁
--     · have : (build_module' ε (mapOutputPorts g (mapInputPorts f e₁))) = none := by
--         have := build_module_type_rename' (ε := ε) (e := e₁) (f := f) (g := g)
--         rw [h] at this; simp_all [mapPorts2]
--       rw [this]; rfl
--     · have this := build_module_type_rename' (ε := ε) (e := e₁) (f := f) (g := g)
--       have this2 := build_module_type_rename' (ε := ε) (e := e₂) (f := f) (g := g)
--       rw [h] at this; dsimp at this; rw [Option.isSome_iff_exists] at this; rcases this with ⟨ a, this ⟩
--       cases h' : build_module' ε e₂
--       · have this3 : (build_module' ε (mapOutputPorts g (mapInputPorts f e₂))) = none := by
--           rw [h'] at this2; simp_all [mapPorts2]
--         rw [this3]; unfold mapPorts2 at *; rw [this]; rfl
--       · rw [h'] at this2; dsimp at this2; rw [Option.isSome_iff_exists] at this2
--         rcases this2 with ⟨a, this2⟩
--         dsimp [mapPorts2] at this this2; rw [this]
--         unfold build_module_type build_module at *
--         unfold mapPorts2 at *
--         dsimp; rw [this2]; dsimp
--         rw [h,this] at he₁
--         rw [h',this2] at he₂
--         simp at *; congr

-- def cast_module {S T} (h : S = T): Module Ident S = Module Ident T := by
--   cases h; rfl

-- def _root_.Sigma.map2 {α t} (pair : @Sigma α t) (f : ∀ {a}, t a → t a) : Sigma t := ⟨ _, f pair.snd ⟩

axiom filterId_correct {α} [DecidableEq α] {m : AssocList α α} {i} :
  m.find? i = some i → m.filterId.find? i = none

axiom filterId_correct2 {α} [DecidableEq α] {m : AssocList α α} {i v} :
  i ≠ v → m.find? i = some v → m.filterId.find? i = some v

axiom inverse_correct {α} [DecidableEq α] {m : AssocList α α} {i v} :
  m.find? i = some v → m.inverse.find? v = some i

theorem mapKey_comm2 {α} {m : PortMap Ident α} {inst : PortMap Ident (InternalPort Ident)} {f i}:
  Function.Bijective f →
  (inst.mapVal fun _ => f).invertible →
  inst.invertible →
  inst.contains i →
  (inst.mapVal fun _ => f).bijectivePortRenaming i = (f ∘ inst.bijectivePortRenaming) i := by
  intro hbij hinv1 hinv2 hcont
  unfold AssocList.bijectivePortRenaming
  rw [hinv1, hinv2]; dsimp
  rw [←AssocList.contains_find?_iff] at hcont
  obtain ⟨v, hfind⟩ := hcont
  by_cases h : i = f i
  · rw [h] at hfind ⊢
    by_cases h' : f i = v
    · subst v
      rw [AssocList.append_find_right, AssocList.append_find_right]
      rw [filterId_correct, filterId_correct]; rw (occs := [2]) [←h]; rfl
      rwa [inverse_correct]
      rw [inverse_correct]
      rw [←AssocList.find?_map_comm]; rw [hfind]; simp [←h]
      rwa [filterId_correct]
      rw [filterId_correct]
      rw [←AssocList.find?_map_comm]; rw [hfind]; simp [←h]
    · rw [AssocList.append_find_left (x := f v)]
      rw [AssocList.append_find_left (x := v)]; rfl
      rw [filterId_correct2] <;> assumption
      rw [filterId_correct2]; rw [←h] at h'; unfold Not at *; intro h''; apply h';
      rwa [←hbij.injective.eq_iff]
      rw [←AssocList.find?_map_comm]
      rw [hfind]; rfl
  · by_cases h' : i = v
    · subst i
      rw [AssocList.append_find_left (x := f v), AssocList.append_find_right]
      rw [filterId_correct]; rfl
      rw [inverse_correct]
      assumption
      rw [filterId_correct]; assumption
      rw [filterId_correct2]; assumption
      rw [←AssocList.find?_map_comm]; rw [hfind]; rfl
    · by_cases h'' : i = f v
      · subst i
        rw [AssocList.append_find_right, AssocList.append_find_left (x := v)]
        dsimp; rw [filterId_correct]; rfl
        rw [inverse_correct]
        rw [←AssocList.find?_map_comm]; rw [hfind]; rfl
        rw [filterId_correct2] <;> assumption
        rw [filterId_correct]
        rw [←AssocList.find?_map_comm]; rw [hfind]; rfl
      · rw [AssocList.append_find_left (x := f v), AssocList.append_find_left (x := v)]; rfl
        rw [filterId_correct2]; assumption; assumption
        rw [filterId_correct2]; assumption
        rw [←AssocList.find?_map_comm]; rw [hfind]; rfl

theorem mapKey_valid_domain {α β γ} [BEq α] [LawfulBEq α] {m : AssocList α β} {f g : α → γ}:
  (∀ i, m.contains i → f i = g i) →
  m.mapKey f = m.mapKey g := by
  induction m with
  | nil => intros; rfl
  | cons k v xs ih =>
    intro h
    simp only [AssocList.mapKey, AssocList.cons.injEq, true_and]; and_intros
    · specialize h k (by simp); assumption
    · apply ih; intro k h'; apply h; simp_all

theorem mapKey_compose {α β γ δ} {m : AssocList α β} {f : α → γ} {g : γ → δ} :
  (m.mapKey f).mapKey g = m.mapKey (g ∘ f) := by
  induction m <;> simpa

/-
Pretty sure these are true based on wf_mapping.  But it also relies on the correctness of bijectivePortRenaming, that it
will actually produce the desired renamings, under the assumption that inst is an invertible map.  It is a bit strange
that the invertibility check needs to be performed twice, once inside of the bijectivePortRenaming function and once
before it to ensure that it will actually perform the renaming correctly.  However, I think this is due to one wanting
to ensure two different properties.  In many cases just having bijectiveness is useful, in others one actually has to
ensure that one is renaming correctly.
-/
theorem mapKey_comm {α} {m : PortMap Ident α} {inst : PortMap Ident (InternalPort Ident)} {f} {hbij : Function.Bijective f}:
  (inst.mapVal (fun _ => f)).invertible →
  inst.invertible →
  (∀ i, AssocList.contains i m → AssocList.contains i inst) →
  m.mapKey ((inst.mapVal fun _ => f).bijectivePortRenaming) = (m.mapKey inst.bijectivePortRenaming).mapKey f := by
  intros; rw [mapKey_valid_domain, mapKey_compose]
  intro i cont; apply mapKey_comm2 <;> solve_by_elim

theorem eraseAll_comm_inputs {S f g i} {Hinj : Function.Injective f} {m : Module Ident S}:
  AssocList.eraseAll (f i) (m.mapPorts2 f g).inputs = AssocList.mapKey f (AssocList.eraseAll i m.inputs) := by
  obtain ⟨min, mout, mint⟩ := m
  unfold Module.mapPorts2 Module.mapInputPorts Module.mapOutputPorts
  exact (AssocList.eraseAll_comm_mapKey (Hinj := Hinj))

theorem eraseAll_comm_outputs {S f g i} {Hinj : Function.Injective g} {m : Module Ident S}:
  AssocList.eraseAll (g i) (m.mapPorts2 f g).outputs = AssocList.mapKey g (AssocList.eraseAll i m.outputs) := by
  obtain ⟨min, mout, mint⟩ := m
  unfold Module.mapPorts2 Module.mapInputPorts Module.mapOutputPorts
  exact (AssocList.eraseAll_comm_mapKey (Hinj := Hinj))

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

theorem keysInMap_iff {α β} [DecidableEq α] {m : AssocList α β} {k} : m.contains k ↔ k ∈ m.keysList := by
  constructor <;> intros
  · solve_by_elim [AssocList.keysInMap]
  · by_cases h' : AssocList.contains k m <;> try assumption
    have h := AssocList.keysNotInMap h'
    contradiction

theorem mapPorts2_unfold_connect {e e' : ExprLow Ident} {f g c} :
  mapPorts2 f g (connect c e) = some e' →
  ∃ e'', mapPorts2 f g e = some e'' ∧ e' = connect { output := g c.output, input := f c.input } e'' := by
  intro h
  dsimp [drunfold] at h
  cases h1 : mapInputPorts f e
  · rw [h1] at h; contradiction
  · rename_i v1; rw [h1] at h; dsimp at h
    dsimp [drunfold] at h
    cases h2 : (mapOutputPorts g v1)
    · rw [h2] at h; contradiction
    · rename_i v2; rw [h2] at h; dsimp [drunfold] at h
      cases h; simp
      unfold mapPorts2
      rw [h1]; assumption

theorem mapPorts2_unfold_product {e₁ e₂ e' : ExprLow Ident} {f g} :
  mapPorts2 f g (product e₁ e₂) = some e' →
  ∃ e₁' e₂', mapPorts2 f g e₁ = some e₁' ∧ mapPorts2 f g e₂ = some e₂' ∧ e' = product e₁' e₂' := by
  intro h
  dsimp [drunfold] at h
  cases h1 : mapInputPorts f e₁ <;> rw [h1] at h <;> try contradiction
  cases h1' : mapInputPorts f e₂ <;> rw [h1'] at h <;> try contradiction
  rename_i v1 v2; dsimp [drunfold] at h
  cases h2 : mapOutputPorts g v1 <;> rw [h2] at h <;> try contradiction
  cases h2' : mapOutputPorts g v2 <;> rw [h2'] at h <;> try contradiction
  rename_i v1' v2'
  dsimp at h; cases h
  exists v1', v2'; and_intros <;> try simp [mapPorts2, *]

theorem rename_build_module_eq {e e' : ExprLow Ident} {f g} (h : Function.Bijective f) (h' : Function.Bijective g) :
  e.wf_mapping ε →
  e.locally_wf →
  e.mapPorts2 f g = .some e' →
  (e'.build_module' ε) = ((e.build_module' ε).map (·.map id (fun _ y => y.mapPorts2 f g))) := by
  induction e generalizing e' with
  | base map typ =>
    intro hwf_mapping hloc heq
    cases hfind : (AssocList.find? typ ε).isSome
    · simp [-AssocList.find?_eq] at hfind
      rw [build_module_unfold_2 hfind]
      simp [drunfold] at heq
      repeat rw [Option.bind_eq_some'] at heq
      obtain ⟨_, h1, heq⟩ := heq
      rw [Option.bind_eq_some] at h1
      obtain ⟨_, h1', heq'⟩ := h1
      cases heq'; simp [drunfold] at heq
      rw [Option.bind_eq_some] at heq
      obtain ⟨_, h1'', heq''⟩ := heq
      cases heq''
      dsimp [drunfold]; rw [hfind]; rfl
    · rw [Option.isSome_iff_exists] at hfind; obtain ⟨m, hfind⟩ := hfind
      rw [build_base_in_env hfind]
      simp [drunfold] at heq
      repeat rw [Option.bind_eq_some'] at heq
      obtain ⟨_, h1, heq⟩ := heq
      rw [Option.bind_eq_some] at h1
      obtain ⟨_, h1', heq'⟩ := h1
      cases heq'; simp [drunfold] at heq
      rw [Option.bind_eq_some] at heq
      obtain ⟨_, h1'', heq''⟩ := heq
      cases heq''
      dsimp [drunfold]; rw [hfind]; dsimp
      obtain ⟨mT, me⟩ := m
      obtain ⟨min, mout, mint⟩ := me; dsimp
      congr
      unfold Module.renamePorts
      dsimp
      unfold Module.mapPorts2
      unfold Module.mapInputPorts Module.mapOutputPorts; dsimp
      congr 1
      · rw [mapKey_comm]
        · rw [Option.guard_eq_some'] at *
          assumption
        · simp [drunfold,all'] at hloc; apply hloc.left
        · unfold wf_mapping at *; rw [hfind] at hwf_mapping; simp at hwf_mapping
          intro i hi
          rw [keysInMap_iff] at hi ⊢
          rwa [List.Perm.mem_iff hwf_mapping.left]
        · assumption
      . rw [mapKey_comm]
        · rw [Option.guard_eq_some'] at *
          assumption
        · simp [drunfold,all'] at hloc; apply hloc.right
        · unfold wf_mapping at *; rw [hfind] at hwf_mapping; simp at hwf_mapping
          intro i hi
          rw [keysInMap_iff] at hi ⊢
          rwa [List.Perm.mem_iff hwf_mapping.right.left]
        · assumption
  | connect c e ih =>
    intro hwf_mapping hloc heq
    dsimp [wf_mapping] at hwf_mapping
    cases hfind : build_module' ε e'
    · obtain ⟨e', heq', e'eq⟩ := mapPorts2_unfold_connect heq; subst_vars
      specialize ih (by assumption) (by assumption) heq'
      dsimp [drunfold] at hfind
      dsimp [drunfold]; rw [Option.bind_eq_none] at hfind
      cases h : build_module' ε e'
      · clear hfind; rw [h] at ih
        symm at ih; rw [Option.map_eq_none'] at ih
        rw [ih]; rfl
      · have := hfind _ h; contradiction
    · obtain ⟨e', heq', e'eq⟩ := mapPorts2_unfold_connect heq; subst_vars
      rename_i val
      specialize ih (by assumption) (by assumption) heq'
      symm at ih; dsimp [drunfold] at hfind; rw [Option.bind_eq_some] at hfind
      obtain ⟨val', hfind', hst⟩ := hfind
      stop
      rw [Option.map_eq_some'] at ih; obtain ⟨m, hbuild1, hbuild2⟩ := ih
      rw [hbuild1]; dsimp [Sigma.map];
      unfold Sigma.map at hbuild2; rename_i val; cases val; cases m; dsimp at *
      cases hbuild2; congr 3
      · rw [eraseAll_comm_inputs (Hinj := h.injective)]
      · rw [eraseAll_comm_outputs (Hinj := h'.injective)]
      · rw [find?_comm_outputs h'.injective, find?_comm_inputs h.injective]; rfl
  | product e₁ e₂ ih₁ ih₂ =>
    intro hwf_mapping
    dsimp [wf_mapping] at hwf_mapping; simp at hwf_mapping
    specialize ih₁ hwf_mapping.1
    specialize ih₂ hwf_mapping.2
    stop
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

theorem refines_mapPorts2_1 {e e' f g} :
  Function.Bijective f → Function.Bijective g → e.wf_mapping ε →
  e.locally_wf →
  e.mapPorts2 f g = some e' →
  ([e| e, ε ]).mapPorts2 f g ⊑ ([e| e', ε]) := by
  unfold build_module_expr; intro hbijf hbijg hwf hloc hmapports;
  unfold build_module; rw [rename_build_module_eq (e := e) (e' := e') (g := g) (f := f)]
  any_goals assumption
  unfold Sigma.map; dsimp
  generalize h : (Option.map (fun x : TModule Ident =>
      (⟨x.fst, x.snd.mapPorts2 f g⟩ : TModule Ident)) (build_module' ε e)).getD ⟨Unit, Module.empty Unit⟩ = y
  have : (fun x : TModule Ident => (⟨x.fst, x.snd.mapPorts2 f g⟩ : TModule Ident)) ⟨Unit, Module.empty Unit⟩
    = ⟨Unit, Module.empty Unit⟩ := rfl
  rw [← this, Option.getD_map] at h; subst y
  apply Module.refines_reflexive

theorem refines_mapPorts2_2 {e e' f g} :
  Function.Bijective f → Function.Bijective g → e.wf_mapping ε →
  e.locally_wf →
  e.mapPorts2 f g = some e' →
  ([e| e', ε]) ⊑ ([e| e, ε ]).mapPorts2 f g := by
  unfold build_module_expr; intro hbijf hbijg hwf hloc hmapports;
  unfold build_module; rw [rename_build_module_eq (e := e) (e' := e') (g := g) (f := f)]
  any_goals assumption
  unfold Sigma.map; dsimp
  generalize h : (Option.map (fun x : TModule Ident =>
      (⟨x.fst, x.snd.mapPorts2 f g⟩ : TModule Ident)) (build_module' ε e)).getD ⟨Unit, Module.empty Unit⟩ = y
  have : (fun x : TModule Ident => (⟨x.fst, x.snd.mapPorts2 f g⟩ : TModule Ident)) ⟨Unit, Module.empty Unit⟩
    = ⟨Unit, Module.empty Unit⟩ := rfl
  rw [← this, Option.getD_map] at h; subst y
  apply Module.refines_reflexive

theorem refines_renamePorts_1 {e e' inst} :
  e.wf_mapping ε → e.locally_wf → e.renamePorts inst = some e' → ([e| e, ε ]).renamePorts inst ⊑ ([e| e', ε]) := by
  intro hwf; unfold renamePorts Module.renamePorts
  solve_by_elim [refines_mapPorts2_1, AssocList.bijectivePortRenaming_bijective]

theorem refines_renamePorts_2 {e e' inst} :
  e.wf_mapping ε → e.locally_wf → e.renamePorts inst = some e' → ([e| e', ε]) ⊑ ([e| e, ε ]).renamePorts inst := by
  intro hwf; unfold renamePorts Module.renamePorts
  solve_by_elim [refines_mapPorts2_2, AssocList.bijectivePortRenaming_bijective]

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

theorem refines_connect {e e' c} :
    wf ε e → wf ε e' →
    [e| e, ε ] ⊑ ([e| e', ε ]) →
    [e| e.connect c, ε ] ⊑ ([e| e'.connect c, ε ]) := by
  intro wf1 wf2 ref
  replace wf1 := wf_builds_module wf1
  replace wf2 := wf_builds_module wf2
  simp only [Option.isSome_iff_exists] at *
  rcases wf1 with ⟨ m₁, wf1 ⟩
  rcases wf2 with ⟨ m₂, wf2 ⟩
  simp only [build_module_expr, build_module, build_module'] at *
  rw [wf1,wf2] at ref ⊢
  solve_by_elim [Module.refines_connect]

attribute [-drunfold] check_eq

theorem check_eq_symm {iexpr iexpr' : ExprLow Ident} :
  iexpr.check_eq iexpr' → iexpr'.check_eq iexpr := by
  induction iexpr generalizing iexpr' <;> unfold check_eq <;> cases iexpr' <;> intro heq
  any_goals contradiction
  · simp_all; and_intros <;> (apply AssocList.EqExt.symm; simp only [*])
  · aesop
  · aesop

axiom check_eq_wf {iexpr iexpr' : ExprLow Ident} :
  iexpr.check_eq iexpr' →
  iexpr.wf ε → iexpr'.wf ε

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
  | connect c e ih =>
    intro iexpr' heq hwf
    have hwf' := check_eq_wf _ ‹_› ‹_›
    cases iexpr' <;> try contradiction
    rename_i c' e'
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
  | connect c e ih =>
    simp [abstract, replace]
    intro hwf
    by_cases h : (connect c e).check_eq expr_pat
    · subst_vars
      simp only [wf,all,Bool.and_eq_true] at hwf
      specialize ih hwf
      rw [h]; dsimp; rw [build_module_unfold_1 hfind]; dsimp
      apply Module.refines_transitive (imod' := (build_module ε expr_pat).snd)
      · apply check_eq_refines; assumption; unfold wf all; aesop
      · rw [Module.renamePorts_empty]; apply Module.refines_reflexive
    · have : wf ε (connect c (e.replace expr_pat (base ∅ i))) := by
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
  | connect c e ih =>
    simp [abstract, replace]
    intro hwf
    by_cases h : (connect c e).check_eq expr_pat
    · subst_vars
      simp only [wf,all,Bool.and_eq_true] at hwf
      specialize ih hwf
      rw [h]; dsimp; rw [build_module_unfold_1 hfind]; dsimp
      apply Module.refines_transitive (imod' := (build_module ε expr_pat).snd)
      · rw [Module.renamePorts_empty]; apply Module.refines_reflexive
      · apply check_eq_refines; apply check_eq_symm; assumption
        apply check_eq_wf; assumption; unfold wf all; aesop
    · have : wf ε (connect c (e.replace expr_pat (base ∅ i))) := by
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
    by_cases h : (base inst typ).check_eq e_pat
    · dsimp [ExprLow.replace]; rw [h]; dsimp [wf, all] at hwf₁
      apply Module.refines_transitive _ Href
      apply check_eq_symm at h; solve_by_elim [check_eq_refines]
    · simp at h; dsimp [ExprLow.replace]; rw [h]
      solve_by_elim [Module.refines_reflexive]
  | product e₁ e₂ ihe₁ ihe₂ =>
    intro hwf hf₁ hf₂ href
    have e₁wf : e₁.wf ε := by simp [all, wf] at hwf ⊢; simp [hwf]
    have e₂wf : e₂.wf ε := by simp [all, wf] at hwf ⊢; simp [hwf]
    dsimp [replace]
    by_cases h : (e₁.product e₂).check_eq e_pat
    · rw [h]; dsimp
      apply Module.refines_transitive _ href
      apply check_eq_symm at h; solve_by_elim [check_eq_refines]
    · simp at h; rw [h]
      apply refines_product <;> solve_by_elim [wf_modify_expression,wf_replace]
  | connect c e =>
    intro hwf hfind₁ hfind₂ href
    dsimp only [replace]
    have e₁wf : e.wf ε := by simp [all, wf] at hwf ⊢; simp [hwf]
    by_cases h : (connect c e).check_eq e_pat
    · rw [h]; dsimp
      apply Module.refines_transitive _ href
      apply check_eq_symm at h; solve_by_elim [check_eq_refines]
    · simp at h; rw [h]
      apply refines_connect <;> solve_by_elim [wf_modify_expression,wf_replace]

-- #print axioms replacement

axiom findInput_iff_contains {e T m i o} :
  build_module' ε e = some ⟨T, m⟩ →
  findInput i e = m.inputs.contains o

axiom findOutput_iff_contains {e T m i o} :
  build_module' ε e = some ⟨T, m⟩ →
  findOutput i e = m.outputs.contains o

axiom wf_comm_connection'_ {e e' : ExprLow Ident} {conn}:
  e.comm_connection'_ conn = .some e' →
  e.wf ε →
  e'.wf ε

axiom refines_comm_base_ {iexpr e' inst typ} :
    iexpr.wf ε → comm_base_ inst typ iexpr = .some e' → [e| e', ε ] ⊑ ([e| iexpr, ε ])

axiom wf_comm_base_ {e e' : ExprLow Ident} {inst typ}:
  e.comm_base_ inst typ = .some e' →
  e.wf ε →
  e'.wf ε

theorem refines_comm_connection'_ {iexpr e' conn} :
    iexpr.wf ε → comm_connection'_ conn iexpr = .some e' → [e| e', ε ] ⊑ ([e| iexpr, ε ]) := by
-- Proof
  unfold build_module_expr
  induction iexpr generalizing e' with
  | base inst typ => intro hwf₁ hcomm; contradiction
  | product e₁ e₂ ihe₁ ihe₂ =>
    intro hwf hcomm
    have e₁wf : e₁.wf ε := by simp [all, wf] at hwf ⊢; simp [hwf]
    have e₂wf : e₂.wf ε := by simp [all, wf] at hwf ⊢; simp [hwf]
    dsimp [comm_connection'_] at hcomm
    split at hcomm
    · cases hcomm; apply ExprLow.refines_product <;> try solve_by_elim [wf_comm_connection'_]
    · cases hcomm; apply ExprLow.refines_product <;> try solve_by_elim [wf_comm_connection'_, Module.refines_reflexive]
    · cases hcomm; apply ExprLow.refines_product <;> try solve_by_elim [wf_comm_connection'_, Module.refines_reflexive]
    · cases hcomm
  | connect c e ih =>
    intro hwf hcomm
    dsimp [comm_connection'_] at hcomm
    split at hcomm
    · split at hcomm <;> try contradiction
      · (split at hcomm <;> try contradiction); cases hcomm
        dsimp [build_module, build_module']
        simp [wf, all, -AssocList.contains_eq] at hwf
        have hbuild_module₁ := wf_builds_module hwf
        simp [Option.isSome_iff_exists ] at hbuild_module₁
        obtain ⟨T₁, e₁, hbuild₁⟩ := hbuild_module₁
        rw [hbuild₁]; dsimp
        apply Module.refines_reflexive_ext
        repeat cases ‹_ ∧ _›; subst_vars
        apply Module.comm_conn_conn_EqExt <;> (symm; assumption)
      · (repeat' (split at hcomm <;> try contradiction)); cases hcomm
        dsimp [build_module, build_module']
        simp [wf, all, -AssocList.contains_eq] at hwf; obtain ⟨hwfl, hwfr⟩ := hwf
        have hbuild_module₁ := wf_builds_module hwfl
        have hbuild_module₂ := wf_builds_module hwfr
        simp [Option.isSome_iff_exists ] at hbuild_module₁ hbuild_module₂
        obtain ⟨T₁, e₁, hbuild₁⟩ := hbuild_module₁
        obtain ⟨T₂, e₂, hbuild₂⟩ := hbuild_module₂
        rw [hbuild₁]; rw [hbuild₂]; dsimp
        rename_i hfi
        apply Module.refines_reflexive_ext
        apply Module.comm_conn_product_EqExt
        · rw [←findOutput_iff_contains] <;> solve_by_elim [hfi.2.1]
        · rw [←findInput_iff_contains] <;> solve_by_elim [hfi.1]
    · simp at hcomm; obtain ⟨e'', hcomm, hconn⟩ := hcomm; subst e'
      apply ExprLow.refines_connect <;> solve_by_elim [wf_comm_connection'_]

theorem refines_comm_connection'_2 {iexpr e' conn} :
    iexpr.wf ε → comm_connection'_ conn iexpr = .some e' → [e| iexpr, ε ] ⊑ ([e| e', ε ]) := by
-- Proof
  unfold build_module_expr
  induction iexpr generalizing e' with
  | base inst typ => intro hwf₁ hcomm; contradiction
  | product e₁ e₂ ihe₁ ihe₂ =>
    intro hwf hcomm
    have e₁wf : e₁.wf ε := by simp [all, wf] at hwf ⊢; simp [hwf]
    have e₂wf : e₂.wf ε := by simp [all, wf] at hwf ⊢; simp [hwf]
    dsimp [comm_connection'_] at hcomm
    split at hcomm
    · cases hcomm; apply ExprLow.refines_product <;> try solve_by_elim [wf_comm_connection'_]
    · cases hcomm; apply ExprLow.refines_product <;> try solve_by_elim [wf_comm_connection'_, Module.refines_reflexive]
    · cases hcomm; apply ExprLow.refines_product <;> try solve_by_elim [wf_comm_connection'_, Module.refines_reflexive]
    · cases hcomm
  | connect c e ih =>
    intro hwf hcomm
    dsimp [comm_connection'_] at hcomm
    split at hcomm
    · split at hcomm <;> try contradiction
      · (split at hcomm <;> try contradiction); cases hcomm
        dsimp [build_module, build_module']
        simp [wf, all, -AssocList.contains_eq] at hwf
        have hbuild_module₁ := wf_builds_module hwf
        simp [Option.isSome_iff_exists ] at hbuild_module₁
        obtain ⟨T₁, e₁, hbuild₁⟩ := hbuild_module₁
        rw [hbuild₁]; dsimp
        apply Module.refines_reflexive_ext
        repeat cases ‹_ ∧ _›; subst_vars
        apply Module.comm_conn_conn_EqExt <;> assumption
      · (repeat' (split at hcomm <;> try contradiction)); cases hcomm
        dsimp [build_module, build_module']
        simp [wf, all, -AssocList.contains_eq] at hwf; obtain ⟨hwfl, hwfr⟩ := hwf
        have hbuild_module₁ := wf_builds_module hwfl
        have hbuild_module₂ := wf_builds_module hwfr
        simp [Option.isSome_iff_exists ] at hbuild_module₁ hbuild_module₂
        obtain ⟨T₁, e₁, hbuild₁⟩ := hbuild_module₁
        obtain ⟨T₂, e₂, hbuild₂⟩ := hbuild_module₂
        rw [hbuild₁]; rw [hbuild₂]; dsimp
        rename_i hfi
        apply Module.refines_reflexive_ext
        apply Module.EqExt.symm
        apply Module.comm_conn_product_EqExt
        · rw [←findOutput_iff_contains] <;> solve_by_elim [hfi.2.1]
        · rw [←findInput_iff_contains] <;> solve_by_elim [hfi.1]
    · simp at hcomm; obtain ⟨e'', hcomm, hconn⟩ := hcomm; subst e'
      apply ExprLow.refines_connect <;> solve_by_elim [wf_comm_connection'_]

theorem refines_fix_point_opt {iexpr e' f n} :
    (∀ e e', e.wf ε → f e = .some e' → ([e| e', ε ] ⊑ ([e| e, ε ])) ∧ e'.wf ε) →
    [e| e', ε ] ⊑ ([e| iexpr, ε ]) →
    e'.wf ε →
    [e| fix_point_opt f e' n , ε ] ⊑ ([e| iexpr, ε ]) := by
-- Proof
  induction n generalizing iexpr e' with
  | zero => intros; simp [fix_point_opt]; assumption
  | succ n ih =>
    intro h href hwf
    dsimp [fix_point_opt]
    split <;> simp
    · have hrand := h _ _ ‹_› ‹_›; apply ih; assumption; apply Module.refines_transitive
      apply hrand.1; solve_by_elim; apply hrand.2
    · assumption

theorem refines_fix_point_opt2' {iexpr e' f n} :
    (∀ e e', e.wf ε → f e = .some e' → ([e| e, ε ] ⊑ ([e| e', ε ])) ∧ e'.wf ε) →
    [e| iexpr, ε ] ⊑ ([e| e', ε ]) →
    e'.wf ε →
    [e| iexpr, ε ] ⊑ ([e| fix_point_opt f e' n, ε ]) := by
-- Proof
  induction n generalizing iexpr e' with
  | zero => intros; simp [fix_point_opt]; assumption
  | succ n ih =>
    intro h href hwf
    dsimp [fix_point_opt]
    split <;> simp
    · have hrand := h _ _ ‹_› ‹_›; apply ih; assumption; apply Module.refines_transitive
      assumption; apply hrand.1; apply hrand.2
    · assumption

theorem wf_fix_point_opt {iexpr f n} :
    (∀ e e', e.wf ε → f e = .some e' → e'.wf ε) →
    iexpr.wf ε →
    (fix_point_opt f iexpr n).wf ε := by
-- Proof
  induction n generalizing iexpr with
  | zero => intros; simp [fix_point_opt]; assumption
  | succ n ih =>
    intro h hwf
    dsimp [fix_point_opt]
    split <;> solve_by_elim

theorem refines_fix_point_opt1 {iexpr f n} :
    (∀ e e', e.wf ε → f e = .some e' → ([e| e', ε ] ⊑ ([e| e, ε ])) ∧ e'.wf ε) →
    iexpr.wf ε →
    [e| fix_point_opt f iexpr n , ε ] ⊑ ([e| iexpr, ε ]) := by
  intros; solve_by_elim [refines_fix_point_opt, Module.refines_reflexive]

theorem refines_fix_point_opt2 {iexpr f n} :
    (∀ e e', e.wf ε → f e = .some e' → ([e| e, ε ] ⊑ ([e| e', ε ])) ∧ e'.wf ε) →
    iexpr.wf ε →
    [e| iexpr, ε ] ⊑ ([e| fix_point_opt f iexpr n, ε ]) := by
  intros; solve_by_elim [refines_fix_point_opt2', Module.refines_reflexive]

theorem refines_foldr' {α} {iexpr e'} {l : List α} (f : α → ExprLow Ident → ExprLow Ident) :
    (∀ e a, e.wf ε → ([e| f a e, ε ] ⊑ ([e| e, ε ])) ∧ (f a e).wf ε) →
    [e| e', ε ] ⊑ ([e| iexpr, ε ]) → e'.wf ε →
    ([e| l.foldr f e', ε ] ⊑ ([e| iexpr, ε ])) ∧ (l.foldr f e').wf ε := by
  induction l generalizing iexpr e' with
  | nil => intros; solve_by_elim
  | cons x xs ih =>
    intro h href hwf; dsimp
    have ⟨ih', ihwf⟩ := ih h href hwf
    have ⟨hrand₁, hrand₂⟩ := h _ x ihwf
    solve_by_elim [Module.refines_transitive]

theorem refines_foldr2' {α} {iexpr e'} {l : List α} (f : α → ExprLow Ident → ExprLow Ident) :
    (∀ e a, e.wf ε → ([e| e, ε ] ⊑ ([e| f a e, ε ])) ∧ (f a e).wf ε) →
    [e| iexpr, ε ] ⊑ ([e| e', ε ]) → e'.wf ε →
    ([e| iexpr, ε ] ⊑ ([e| l.foldr f e', ε ])) ∧ (l.foldr f e').wf ε := by
  induction l generalizing iexpr e' with
  | nil => intros; solve_by_elim
  | cons x xs ih =>
    intro h href hwf; dsimp
    have ⟨ih', ihwf⟩ := ih h href hwf
    have ⟨hrand₁, hrand₂⟩ := h _ x ihwf
    solve_by_elim [Module.refines_transitive]

theorem refines_foldr {α} {iexpr} {l : List α} (f : α → ExprLow Ident → ExprLow Ident) :
    (∀ e a, e.wf ε → ([e| f a e, ε ] ⊑ ([e| e, ε ])) ∧ (f a e).wf ε) → iexpr.wf ε →
    ([e| l.foldr f iexpr, ε ] ⊑ ([e| iexpr, ε ])) := by
  intros; exact refines_foldr' (l := l) ε f ‹_› Module.refines_reflexive ‹_› |>.1

theorem refines_foldr2 {α} {iexpr} {l : List α} (f : α → ExprLow Ident → ExprLow Ident) :
    (∀ e a, e.wf ε → ([e| e, ε ] ⊑ ([e| f a e, ε ])) ∧ (f a e).wf ε) → iexpr.wf ε →
    ([e| iexpr, ε ] ⊑ ([e| l.foldr f iexpr, ε ])) := by
  intros; exact refines_foldr2' (l := l) ε f ‹_› Module.refines_reflexive ‹_› |>.1

theorem wf_foldr {α} {iexpr} {l : List α} (f : α → ExprLow Ident → ExprLow Ident) :
    (∀ e a, e.wf ε → ([e| f a e, ε ] ⊑ ([e| e, ε ])) ∧ (f a e).wf ε) → iexpr.wf ε → (l.foldr f iexpr).wf ε := by
  intros; exact refines_foldr' (l := l) ε f ‹_› Module.refines_reflexive ‹_› |>.2

theorem refines_comm_bases {iexpr l} :
  iexpr.wf ε → [e| comm_bases l iexpr, ε ] ⊑ ([e| iexpr, ε ]) := by
  unfold comm_bases; intro hwf
  apply refines_foldr
  · intros; and_intros
    · unfold Function.uncurry; unfold comm_base
      apply refines_fix_point_opt1; intros; and_intros
      all_goals solve_by_elim [refines_comm_base_, wf_comm_base_]
    · unfold Function.uncurry; unfold comm_base
      apply wf_fix_point_opt; intros
      all_goals solve_by_elim [wf_comm_base_]
  · assumption

theorem refines_comm_connections' {iexpr l} :
  iexpr.wf ε → [e| comm_connections' l iexpr, ε ] ⊑ ([e| iexpr, ε ]) := by
  unfold comm_connections'; intro hwf
  apply refines_foldr
  · intros; and_intros
    · unfold comm_connection'
      apply refines_fix_point_opt1; intros; and_intros
      all_goals solve_by_elim [refines_comm_connection'_, wf_comm_connection'_]
    · unfold comm_connection'
      apply wf_fix_point_opt; intros
      all_goals solve_by_elim [refines_comm_connection'_, wf_comm_connection'_]
  · assumption

theorem refines_comm_connections2' {iexpr l} :
  iexpr.wf ε → [e| iexpr, ε ] ⊑ ([e| comm_connections' l iexpr, ε ]) := by
  unfold comm_connections'; intro hwf
  apply refines_foldr2
  · intros; and_intros
    · unfold comm_connection'
      apply refines_fix_point_opt2; intros; and_intros
      all_goals solve_by_elim [refines_comm_connection'_2, wf_comm_connection'_]
    · unfold comm_connection'
      apply wf_fix_point_opt; intros
      all_goals solve_by_elim [refines_comm_connection'_, wf_comm_connection'_]
  · assumption

axiom ensureIOUnmodified_correct {e : ExprLow Ident} {p} :
  e.ensureIOUnmodified p → [e| e, ε ].renamePorts p = ([e| e, ε ])

theorem force_replace_eq_replace {e e₁ e₂ : ExprLow Ident} :
    (e.force_replace e₁ e₂).1 = e.replace e₁ e₂ := by
  induction e <;> simp [force_replace, replace] <;> split <;> simp [*]

axiom refines_subset {e e' : ExprLow Ident} (ε' : IdentMap Ident (Σ T : Type, Module Ident T)) :
  ε.subsetOf ε' → e.wf ε → e'.wf ε →
  [e| e, ε ] ⊑ ([e| e', ε ]) →
  [e| e, ε' ] ⊑ ([e| e', ε' ])

end Refinement

end ExprLow
end DataflowRewriter
