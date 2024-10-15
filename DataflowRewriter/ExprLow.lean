/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.Module
import DataflowRewriter.Simp
import DataflowRewriter.HVector

namespace DataflowRewriter

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
  | base : Ident → Ident → ExprLow Ident
  | input : InternalPort Ident → Ident → ExprLow Ident → ExprLow Ident
  | output : InternalPort Ident → Ident → ExprLow Ident → ExprLow Ident
  | product : ExprLow Ident → ExprLow Ident → ExprLow Ident
  | connect : InternalPort Ident → InternalPort Ident → ExprLow Ident → ExprLow Ident
  deriving Repr, Hashable, Ord, Inhabited, DecidableEq

namespace ExprLow

variable {Ident}
variable [DecidableEq Ident]

def get_types (ε : IdentMap Ident (Σ T, Module Ident T)) (i : Ident) : Type* :=
  (ε.find? i) |>.map Sigma.fst |>.getD PUnit

def ident_list : ExprLow Ident → List Ident
  | .base i e => [e]
  | .input _ _ e
  | .output _ _ e
  | .connect _ _ e => e.ident_list
  | .product a b => a.ident_list ++ b.ident_list

abbrev EType ε (e : ExprLow Ident) := HVector (get_types ε) e.ident_list

@[drunfold] def build_moduleD (ε : IdentMap Ident ((T: Type) × Module Ident T))
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
  | .input a b e' => do
    let e ← build_moduleD ε e'
    return e.renameToInput (λ p => if p == a then ⟨ .top, b ⟩ else p)
  | .output a b e' => do
    let e ← build_moduleD ε e'
    return e.renameToOutput (λ p => if p == a then ⟨ .top, b ⟩ else p)
  | .connect o i e' => do
    let e ← build_moduleD ε e'
    return e.connect' o i
  | .product a b => do
    let a ← build_moduleD ε a;
    let b ← build_moduleD ε b;
    return a.productD b

theorem build_module'.dep_rewrite {instIdent} : ∀ {modIdent : Ident} {ε a} (Hfind : ε.find? modIdent = a),
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

@[drunfold] def build_module' (ε : IdentMap Ident ((T: Type) × Module Ident T))
    : (e : ExprLow Ident) → Option (Σ T, Module Ident T)
  | .base i e => do
    let mod ← ε.find? e
    return ⟨ _, mod.2.renamePorts λ ⟨ _, y ⟩ => ⟨ .internal i, y ⟩ ⟩
  | .input a b e' => do
    let e ← build_module' ε e'
    return ⟨ _, e.2.renameToInput (λ p => if p == a then ⟨ .top, b ⟩ else p) ⟩
  | .output a b e' => do
    let e ← build_module' ε e'
    return ⟨ _, e.2.renameToOutput (λ p => if p == a then ⟨ .top, b ⟩ else p) ⟩
  | .connect o i e' => do
    let e ← build_module' ε e'
    return ⟨ _, e.2.connect' o i ⟩
  | .product a b => do
    let a ← build_module' ε a;
    let b ← build_module' ε b;
    return ⟨ _, a.2.product b.2 ⟩

@[drunfold] def build_moduleP (ε : IdentMap Ident (Σ T, Module Ident T))
    (e : ExprLow Ident)
    (h : (build_module' ε e).isSome = true := by rfl)
    : Σ T, Module Ident T := build_module' ε e |>.get h

@[drunfold] def build_module (ε : IdentMap Ident (Σ T, Module Ident T))
    (e : ExprLow Ident)
    : Σ T, Module Ident T := build_module' ε e |>.getD ⟨ Unit, Module.empty _ ⟩

@[drunfold] abbrev build_module_expr (ε : IdentMap Ident (Σ T, Module Ident T))
    (e : ExprLow Ident)
    : Module Ident (build_module ε e).1 := (build_module ε e).2

@[drunfold] abbrev build_module_type (ε : IdentMap Ident (Σ T, Module Ident T))
    (e : ExprLow Ident)
    : Type _ := (build_module ε e).1

notation:25 "[e| " e ", " ε " ]" => build_module_expr ε e
notation:25 "[T| " e ", " ε " ]" => build_module_type ε e

-- theorem build_module_replace {ε : IdentMap Ident (Σ (T : Type), Module Ident T)} {expr} {m : (Σ (T : Type), Module Ident T)} {i : Ident} :
--   (build_module' ε expr).isSome → (build_module' (ε.replace i m) expr).isSome := by sorry

def _root_.DataflowRewriter.IdentMap.replace_env (ε : IdentMap Ident (Σ (T : Type _), Module Ident T)) {ident mod}
  (h : ε.mem ident mod) mod' :=
  (ε.replace ident mod')

notation:25 "{" ε " | " h " := " mod' "}" => IdentMap.replace_env ε h mod'

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

-- set_option debug.skipKernelTC true in
set_option pp.proofs true in
set_option pp.deepTerms true in
variable {T T'}
         {mod : Module Ident T}
         {mod' : Module Ident T'} in
theorem substitution (iexpr : ExprLow Ident) {ident} (h : ε.mem ident ⟨ T, mod ⟩) :
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
  | input iport name e iH => sorry
  | output iport name e iH => sorry
  | product e₁ e₂ iH₁ iH₂ => sorry
  | connect p1 p2 e iH => sorry

end Refinement

end ExprLow
end DataflowRewriter
