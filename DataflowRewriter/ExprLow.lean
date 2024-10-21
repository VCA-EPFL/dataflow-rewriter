/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.Module
import DataflowRewriter.Simp
import DataflowRewriter.HVector

namespace DataflowRewriter

structure PortMapping (Ident) where
  input : PortMap Ident (InternalPort Ident)
  output : PortMap Ident (InternalPort Ident)
deriving Repr, Inhabited, DecidableEq

namespace PortMapping

variable {Ident}

def append (a b : PortMapping Ident) :=
  PortMapping.mk (a.input ++ b.input) (a.output ++ b.output)

instance : Append (PortMapping Ident) := ⟨append⟩

instance : EmptyCollection (PortMapping Ident) := ⟨⟨∅, ∅⟩⟩

end PortMapping

structure Interface (Ident) where
  input : List (InternalPort Ident)
  output : List (InternalPort Ident)

namespace Interface

variable {Ident}

def isBaseModule (i : Interface Ident) : Bool :=
  i.input.all (·.inst.isTop) && i.output.all (·.inst.isTop)

def toPortMapping (i : Interface Ident) (ident : Ident) : PortMapping Ident :=
  if i.isBaseModule
  then ⟨(i.input.map (λ a => (a, InternalPort.mk (.internal ident) a.name))).toAssocList,
        (i.output.map (λ a => (a, InternalPort.mk (.internal ident) a.name))).toAssocList⟩
  else ∅

end Interface

namespace Module

section

variable {S Ident}
variable [DecidableEq Ident]

def renamePorts (m : Module Ident S) (p : PortMapping Ident) : Module Ident S :=
  m.mapInputPorts (λ k => p.input.find? k |>.getD k)
  |>.mapOutputPorts (λ k => p.output.find? k |>.getD k)

def toInterface (m : Module Ident S): Interface Ident :=
  ⟨m.inputs.keysList, m.outputs.keysList⟩

end

section

variable {S Ident}

theorem mapInputPorts_id {m : Module Ident S} :
  m.mapInputPorts id = m := by
  unfold mapInputPorts
  rw [Batteries.AssocList.mapKey_toList]; simp

theorem mapOutputPorts_id {m : Module Ident S} :
  m.mapOutputPorts id = m := by
  unfold mapOutputPorts
  rw [Batteries.AssocList.mapKey_toList]; simp

variable [DecidableEq Ident]

theorem renamePorts_empty {m : Module Ident S} :
  m.renamePorts ∅ = m := by
  unfold renamePorts
  have : (fun k => (Batteries.AssocList.find? k (∅ : PortMapping Ident).output).getD k) = id := by rfl
  have : (fun k => (Batteries.AssocList.find? k (∅ : PortMapping Ident).input).getD k) = id := by rfl
  simp only [*, mapInputPorts_id, mapOutputPorts_id]

end

end Module

namespace IdentMap

variable {Ident}

def toInterface (i : IdentMap Ident (TModule Ident)) : IdentMap Ident (Interface Ident) :=
  i.mapVal (λ _ x => x.snd |>.toInterface)

end IdentMap

/--
ExprLow is an inductive definition of a circuit, inspired by a definition by
Tony Law [?].  The main difference is th edadition of input and output
constructors that essentially just rename a port to a top-level IO port.

An alternative definition of IO ports was considered, in that they could just be
a `base` module.  This has advantages because it makes the definition more
uniform, however, when building a `Module` from an `ExprLow`, one would have
additional state to be able to communicate from an input to the input for the
module.
-/
inductive ExprLow Ident where
| base : PortMapping Ident → Ident → ExprLow Ident
| product : ExprLow Ident → ExprLow Ident → ExprLow Ident
| connect : InternalPort Ident → InternalPort Ident → ExprLow Ident → ExprLow Ident
deriving Repr, Inhabited, DecidableEq

inductive NamedExprLow Ident where
| input : InternalPort Ident → Ident → NamedExprLow Ident → NamedExprLow Ident
| output : InternalPort Ident → Ident → NamedExprLow Ident → NamedExprLow Ident
| base : ExprLow Ident → NamedExprLow Ident
deriving Repr, Inhabited, DecidableEq

namespace ExprLow

variable {Ident}
variable [DecidableEq Ident]

@[drunfold] def modify (i i' : Ident) : ExprLow Ident → ExprLow Ident
| .base inst typ => if typ = i then .base inst i' else .base inst typ
| .connect x y e' => modify i i' e' |> .connect x y
| .product e₁ e₂ =>
  let e₁' := e₁.modify i i'
  let e₂' := e₂.modify i i'
  .product e₁' e₂'

@[drunfold] def replace (e e_sub e_new : ExprLow Ident) : ExprLow Ident :=
  if e = e_sub then e_new else
  match e with
  | .base inst typ => e
  | .connect x y e_sub' => .connect x y (e_sub'.replace e_sub e_new)
  | .product e_sub₁ e_sub₂ =>
    .product (e_sub₁.replace e_sub e_new) (e_sub₂.replace e_sub e_new)

@[drunfold]
def abstract (e e_sub : ExprLow Ident) (i_inst : PortMapping Ident) (i_typ : Ident) : ExprLow Ident :=
  .base i_inst i_typ |> e.replace e_sub

@[drunfold]
def concretise (e e_sub : ExprLow Ident) (i_inst : PortMapping Ident) (i_typ : Ident) : ExprLow Ident :=
  .base i_inst i_typ |> (e.replace · e_sub)

@[drunfold]
def calc_mapping : ExprLow Ident → PortMapping Ident
| .base inst typ => inst
| .connect _x _y e => e.calc_mapping
| .product e₁ e₂ => e₁.calc_mapping ++ e₂.calc_mapping

variable (ε : IdentMap Ident (Σ T : Type _, Module Ident T))

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

def all (P : Ident → Bool) : ExprLow Ident → Bool
| base f typ => P typ
| connect o i e => e.all P
| product e₁ e₂ => e₁.all P && e₂.all P

def any (P : Ident → Bool) : ExprLow Ident → Bool
| base f typ => P typ
| connect o i e => e.any P
| product e₁ e₂ => e₁.any P || e₂.any P

def wf : ExprLow Ident → Bool := all (λ typ => ε.contains typ)

def excludes (ident : Ident) : ExprLow Ident → Bool := all (· ≠ ident)

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

-- theorem build_module_replace {ε : IdentMap Ident (Σ (T : Type), Module Ident T)} {expr} {m : (Σ (T : Type), Module Ident T)} {i : Ident} :
--   (build_module' ε expr).isSome → (build_module' (ε.replace i m) expr).isSome := by sorry

theorem find?_modify {modIdent ident m m'} {ε : IdentMap Ident (Σ (T : Type _), Module Ident T)}
  (h : ε.mem ident m') :
  Batteries.AssocList.find? modIdent ε = none →
  Batteries.AssocList.find? modIdent ({ε | h := m}) = none := by sorry

theorem find?_modify2 {modIdent m m'} {ε : IdentMap Ident (Σ (T : Type _), Module Ident T)}
  (h : ε.mem modIdent m') :
  Batteries.AssocList.find? modIdent ({ε | h := m}) = m := by sorry

theorem find?_modify3 {modIdent ident m m' m''} {ε : IdentMap Ident (Σ (T : Type _), Module Ident T)}
  (h : ε.mem ident m') :
  modIdent ≠ ident →
  Batteries.AssocList.find? modIdent ε = some m'' →
  Batteries.AssocList.find? modIdent ({ε | h := m}) = some m'' := by sorry

-- instance
--   {ε : IdentMap Ident (Σ (T : Type _), Module Ident T)}
--   {S ident iexpr} {mod : Σ T : Type _, Module Ident T}
--   {mod' : Σ T : Type _, Module Ident T} {smod : Module Ident S}
--   {h : ε.mem ident mod}
--   [MatchInterface mod.2 mod'.2]
--   [MatchInterface ([e| iexpr, ε ]) smod]
--   : MatchInterface ([e| iexpr, {ε | h := mod'} ]) smod := by sorry

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
  simp at ref1 ref2 ⊢
  clear wf1 wf2 wf3 wf4
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
  simp; solve_by_elim [Module.refines_connect]

-- set_option debug.skipKernelTC true in
set_option pp.proofs true in
set_option pp.deepTerms true in
variable {T T'}
         {mod : Module Ident T}
         {mod' : Module Ident T'} in
theorem substite_env (iexpr : ExprLow Ident) {ident} (h : ε.mem ident ⟨ T, mod ⟩) :
    mod ⊑ mod' →
    [e| iexpr, ε ] ⊑ ([e| iexpr, {ε | h := ⟨ T', mod' ⟩} ]) := by
  unfold build_module_expr
  induction iexpr with
  | base instIdent modIdent =>
    intro Hmod
    dsimp [build_module_expr, build_module, build_module']
    cases Hfind : Batteries.AssocList.find? modIdent ε with
    | none =>
      have Hfind' := find?_modify (m := ⟨T', mod'⟩) h Hfind
      rw [Hfind'] -- simp does not work
      apply Module.refines_reflexive
    | some curr_mod =>
      by_cases h : modIdent = ident
      · subst_vars
        have Hfind' := find?_modify2 (m := ⟨ T', mod' ⟩) h
        rw [Hfind']; simp
        -- rw [Hfind] at Hbase; simp at Hbase
        sorry
      · sorry
  | product e₁ e₂ iH₁ iH₂ => sorry
  | connect p1 p2 e iH => sorry

theorem substition {I I' i i' mod mod' iexpr} :
    ε.find? i = some ⟨ I, mod ⟩ →
    ε.find? i' = some ⟨ I', mod' ⟩ →
    mod ⊑ mod' →
    [e| iexpr, ε ] ⊑ ([e| iexpr.modify i i', ε ]) := by
  unfold build_module_expr
  induction iexpr generalizing i i' mod mod' with
  | base inst typ =>
    intro hfind₁ hfind₂ Href
    dsimp [drunfold]
    by_cases h : typ = i
    · subst typ
      rw [hfind₁]; dsimp [drunfold]
      sorry
    · sorry
  | _ => sorry

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
      rw [Module.renamePorts_empty]; apply Module.refines_reflexive
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
      rw [build_module_unfold_1 hfind, Module.renamePorts_empty]
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
    · rw [build_module_unfold_1 hfind, Module.renamePorts_empty]
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
      rw [Module.renamePorts_empty]; apply Module.refines_reflexive
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
      rw [build_module_unfold_1 hfind, Module.renamePorts_empty]
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
    · rw [build_module_unfold_1 hfind, Module.renamePorts_empty]
      apply Module.refines_reflexive
    · have : wf ε (connect x y (e.replace expr_pat (base ∅ i))) := by
        simp [wf, all]
        convert_to wf ε (e.replace expr_pat (base ∅ i));
        simp [wf, all]
        apply wf_replace; assumption; simp only [wf, all]
        skip; apply Batteries.AssocList.contains_some2; rw [hfind]; rfl
      solve_by_elim [refines_connect]

end Refinement

end ExprLow
end DataflowRewriter
