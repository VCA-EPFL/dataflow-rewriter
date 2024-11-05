/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Lean
import Init.Data.BitVec.Lemmas
import Qq

import DataflowRewriter.Simp
import DataflowRewriter.Module
import DataflowRewriter.ExprLow
import DataflowRewriter.Component
import DataflowRewriter.KernelRefl
import DataflowRewriter.Reduce
import DataflowRewriter.List
import DataflowRewriter.ExprHighLemmas
import DataflowRewriter.Tactic
import DataflowRewriter.Rewrites.MuxTaggedRewrite

open Batteries (AssocList)

open Lean hiding AssocList
open Meta Elab

namespace DataflowRewriter.MuxTaggedRewrite

attribute [drcompute] Batteries.AssocList.toList Function.uncurry Module.mapIdent List.toAssocList List.foldl Batteries.AssocList.find? Option.pure_def Option.bind_eq_bind Option.bind_some Module.renamePorts Batteries.AssocList.mapKey InternalPort.map toString Nat.repr Nat.toDigits Nat.toDigitsCore Nat.digitChar List.asString Option.bind Batteries.AssocList.mapVal Batteries.AssocList.eraseAll Batteries.AssocList.eraseP beq_self_eq_true Option.getD cond beq_self_eq_true  beq_iff_eq  InternalPort.mk.injEq  String.reduceEq  and_false  imp_self BEq.beq

attribute [drdecide] InternalPort.mk.injEq and_false decide_False decide_True and_true Batteries.AssocList.eraseAllP  InternalPort.mk.injEq
  and_false  decide_False  decide_True  reduceCtorEq  cond  List.map

abbrev Ident := Nat

def ε (Tag T : Type _) : IdentMap String (TModule String) :=
  [ ("join", ⟨ _, StringModule.join Tag T ⟩)
  , ("mux", ⟨ _, StringModule.mux T ⟩)
  , ("tagged_mux", ⟨ _, StringModule.mux (Tag × T) ⟩)
  , ("fork", ⟨ _, StringModule.fork Tag 2 ⟩)
  ].toAssocList

def lhsNames := rewrite.input_expr.build_module_names
def rhsNames := rewrite.output_expr.build_module_names

def lhsModuleType (Tag T : Type _) : Type := by
  precomputeTac [T| rewrite.input_expr, ε Tag T ] by
    dsimp only [drunfold,seval,drcompute]

@[drunfold] def lhsModule (Tag T : Type _) : StringModule (lhsModuleType Tag T) := by
  precomputeTac [e| rewrite.input_expr, ε Tag T ] by
    dsimp only [drunfold,seval,drcompute]
    simp only [seval,drdecide]
    conv in Module.connect'' _ _ => rw [Module.connect''_dep_rw]; rfl
    dsimp

def rhsModuleType (Tag T : Type _) : Type := by
  precomputeTac [T| rewrite.output_expr, ε Tag T ] by
    dsimp only [drunfold,seval,drcompute]

-- #reduce rhsNames
-- #reduce rhsModuleType

@[drunfold] def rhsModule (Tag T : Type _) : StringModule (rhsModuleType Tag T) := by
  precomputeTac [e| rewrite.output_expr, ε Tag T ] by
    dsimp only [drunfold,seval,drcompute]
    simp only [seval,drdecide]
    conv in Module.connect'' _ _ => rw [Module.connect''_dep_rw]; rfl
    conv in _ :: Module.connect'' _ _ :: _ => arg 2; rw [Module.connect''_dep_rw]; rfl
    conv in _ :: Module.connect'' _ _ :: _ => arg 2; arg 2; rw [Module.connect''_dep_rw]; rfl
    conv in _ :: Module.connect'' _ _ :: _ => arg 2; arg 2; arg 2; rw [Module.connect''_dep_rw]; rfl
    dsimp

attribute [dmod] Batteries.AssocList.find? BEq.beq

instance {Tag T} : MatchInterface (rhsModule Tag T) (lhsModule Tag T) where
  input_types := by
    intro ident;
    by_cases h : (Batteries.AssocList.contains ↑ident (rhsModule Tag T).inputs)
    · have h' := AssocList.keysInMap h; fin_cases h' <;> rfl
    · have h' := AssocList.keysNotInMap h; dsimp [drunfold, AssocList.keysList] at h' ⊢
      simp at h'; let ⟨ ha, hb, hc ⟩ := h'; clear h'
      simp only [Batteries.AssocList.find?_eq, Batteries.AssocList.toList]
      rcases ident with ⟨ i1, i2 ⟩;
      repeat (rw [List.find?_cons_of_neg]; rotate_left; simp; intros; subst_vars; solve_by_elim)
      sorry
  output_types := by
    intro ident;
    by_cases h : (Batteries.AssocList.contains ↑ident (rhsModule Tag T).outputs)
    · have h' := AssocList.keysInMap h; fin_cases h' <;> rfl
    · have h' := AssocList.keysNotInMap h; dsimp [drunfold, AssocList.keysList] at h' ⊢
      simp at h'
      simp only [Batteries.AssocList.find?_eq, Batteries.AssocList.toList]
      rcases ident with ⟨ i1, i2 ⟩;
      repeat (rw [List.find?_cons_of_neg]; rotate_left; simp; intros; subst_vars; solve_by_elim)
      rfl
  inputs_present := by sorry
  outputs_present := by sorry

#reduce rhsNames
#reduce rhsModuleType

#reduce lhsNames
#reduce lhsModuleType


def φ {Tag T} (state_rhs : rhsModuleType Tag T) (state_lhs : lhsModuleType Tag T) : Prop :=
  state_rhs.2.2.1.2 ++ state_rhs.2.1.1.map Prod.snd  = state_lhs.2.1 ++ state_lhs.1.2 ∧
  state_rhs.2.2.2.2 ++ state_rhs.2.1.2.1.map Prod.snd  = state_lhs.2.2.1 ++ state_lhs.1.2 ∧
  state_rhs.2.1.2.2 = state_lhs.2.2.2 ∧
  state_rhs.1 ++ state_rhs.2.2.1.1 ++ state_rhs.2.1.1.map Prod.fst = state_lhs.1.1 ∧
  state_rhs.1 ++ state_rhs.2.2.2.1 ++ state_rhs.2.1.2.1.map Prod.fst = state_lhs.1.1

theorem sigma_rw {S T : Type _} {m m' : Σ (y : Type _), S → y → T → Prop} {x : S} {y : T} {v : m.fst}
        (h : m = m' := by reduce; rfl) :
  m.snd x v y ↔ m'.snd x (h ▸ v) y := by
  constructor <;> (intros; subst h; assumption)

theorem φ_indistinguishable {Tag T} :
  ∀ x y, φ x y → Module.indistinguishable (rhsModule Tag T) (lhsModule Tag T) x y := by
  unfold φ; intro x y H
  constructor <;> intro ident new_i v Hcontains Hsem
  . have Hkeys := AssocList.keysInMap Hcontains; clear Hcontains
    fin_cases Hkeys
    . simp [drunfold,drcompute,seval]
      constructor; rw[sigma_rw]

  · have Hkeys := keysInMap Hcontains; clear Hcontains
    fin_cases Hkeys
    let ⟨ ⟨ i, Ha, Hc ⟩, Hb ⟩ := Hsem; clear Hsem
    let (x1, x2) := x; clear x
    let (new_i1, new_i2) := new_i; clear new_i
    subst_vars; dsimp at *
    generalize h : x2[i] = y'
    have Ht : ∃ (i : Fin x2.length), x2.get i = y' := by exists i
    rw [← List.mem_iff_get] at Ht
    have He := List.Perm.symm H
    have Hiff := List.Perm.mem_iff (a := y') He
    have Ht' : y' ∈ y := by rw [Hiff]; simp; cases Ht <;> tauto
    rw [List.mem_iff_get] at Ht'
    let ⟨ i', Hi' ⟩ := Ht'; clear Ht'
    constructor; exists i'; and_intros; rfl
    simp [←Hi']

theorem correct_threeway_merge'' {Tag T: Type _} [DecidableEq T]:
  rhsModule Tag T ⊑_{φ} lhsModule Tag T := by
  intro x y HPerm
  constructor
  all_goals sorry

end DataflowRewriter.MuxTaggedRewrite
