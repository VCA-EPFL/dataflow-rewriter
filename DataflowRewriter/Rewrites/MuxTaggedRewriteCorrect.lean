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
    unfold Module.connect''
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
  state_rhs.1 ++ state_rhs.2.2.2.1 ++ state_rhs.2.1.2.1.map Prod.fst = state_lhs.1.1 ∧
  (state_lhs.2.2.2.getLast? = some true → state_lhs.2.1 = []) ∧
  (state_lhs.2.2.2.getLast? = some false → state_lhs.2.2.1 = [])

def φ' {Tag T} (state_rhs : rhsModuleType Tag T) (state_lhs : lhsModuleType Tag T) : Prop :=
  state_rhs.2.2.1.2 ++ state_rhs.2.1.1.map Prod.snd  = state_lhs.2.1 ++ state_lhs.1.2 ∧
  state_rhs.2.2.2.2 ++ state_rhs.2.1.2.1.map Prod.snd  = state_lhs.2.2.1 ++ state_lhs.1.2 ∧
  state_rhs.2.1.2.2 = state_lhs.2.2.2 ∧
  state_rhs.1 ++ state_rhs.2.2.1.1 ++ state_rhs.2.1.1.map Prod.fst = state_lhs.1.1 ∧
  state_rhs.1 ++ state_rhs.2.2.2.1 ++ state_rhs.2.1.2.1.map Prod.fst = state_lhs.1.1


theorem lhs_internal_correctness {Tag T}:
  ∀ (x : rhsModuleType Tag T) (y : lhsModuleType Tag T), φ' x y -> ∃ y',
    existSR [fun st st' =>  ∃ a b a_1 a_2 b_1 output,
              ((b_1 ++ [false] = st.2.2.2 ∧ a_1 = st.2.1 ∧ a_2 ++ [output] = st.2.2.1 ∨
              b_1 ++ [true] = st.2.2.2 ∧ a_1 ++ [output] = st.2.1 ∧ a_2 = st.2.2.1) ∧
              st.1 = (a, b)) ∧
              (st'.1.2 = output :: b ∧ st'.1.1 = a) ∧ (a_1, a_2, b_1) = st'.2] y y'
    ∧ φ x y' := by sorry


@[reducible] def cast_first {β : Type _ → Type _} {a b : (Σ α, β α)} (h : a = b) : a.fst = b.fst := by
  subst_vars; rfl

theorem sigma_rw {S T : Type _} {m m' : Σ (y : Type _), S → y → T → Prop} {x : S} {y : T} {v : m.fst}
        (h : m = m' := by reduce; rfl) :
  m.snd x v y ↔ m'.snd x ((cast_first h).mp v) y := by
  constructor <;> (intros; subst h; assumption)

theorem sigma_rw_simp {S T : Type _} {m m' : Σ (y : Type _), S → y → T → Prop} {x : S} {y : T} {v : m.fst}
        (h : m = m' := by simp [drunfold,drcompute,seval]; rfl) :
  m.snd x v y ↔ m'.snd x ((cast_first h).mp v) y := by
  constructor <;> (intros; subst h; assumption)

set_option maxHeartbeats 0

theorem φ_indistinguishable {Tag T} :
  ∀ x y, φ x y → Module.indistinguishable (rhsModule Tag T) (lhsModule Tag T) x y := by
  unfold φ; intro ⟨x_fork, ⟨x_muxT, x_muxF, x_muxC⟩, ⟨x_join1_l, x_join1_r⟩, ⟨x_join2_l, x_join2_r⟩⟩ ⟨⟨y_join_l, y_join_r⟩, ⟨y_muxT, y_muxF, y_muxC⟩⟩ H
  dsimp at *
  constructor <;> intro ident new_i v Hcontains Hsem
  . have Hkeys := AssocList.keysInMap Hcontains; clear Hcontains
    fin_cases Hkeys
    . simp [drunfold,drcompute,seval] at Hsem ⊢
      rw[sigma_rw_simp] at Hsem; simp at Hsem
      --rcases y_join with ⟨y_join_l, y_join_r⟩
      apply Exists.intro ((_, _), (_, (_, _)))
      constructor; dsimp; and_intros
      all_goals rfl
    . simp [drunfold,drcompute,seval] at Hsem ⊢
      rw[sigma_rw_simp] at Hsem; simp at Hsem
      apply Exists.intro ((_, _), (_, (_, _)))
      constructor; dsimp; and_intros
      all_goals rfl
    . simp [drunfold,drcompute,seval] at Hsem ⊢
      rw[sigma_rw_simp] at Hsem; simp at Hsem
      apply Exists.intro ((_, _), (_, (_, _)))
      constructor; dsimp; and_intros
      all_goals rfl
    . simp [drunfold,drcompute,seval] at Hsem ⊢
      rw[sigma_rw_simp] at Hsem; simp at Hsem
      --rcases y_join with ⟨y_join_l, y_join_r⟩
      apply Exists.intro ((_, _), (_, (_, _)))
      constructor; dsimp; and_intros
      all_goals rfl
  · have Hkeys := AssocList.keysInMap Hcontains; clear Hcontains
    rcases new_i with ⟨x_new_fork, ⟨x_new_muxT, x_new_muxF, x_new_muxC⟩, ⟨x_new_join1_l, x_new_join1_r⟩, ⟨x_new_join2_l, x_new_join2_r⟩⟩
    fin_cases Hkeys
    . simp [drunfold,drcompute,seval] at Hsem ⊢
      rw[sigma_rw_simp] at Hsem; simp at Hsem
      rcases H with ⟨ H₁, H₂, H₃, H₄, H₅, H₆, H₇ ⟩
      rcases v with ⟨ vt, vv ⟩
      rcases Hsem with ⟨ ⟨ ⟨hsemll₁, hsemll₂, hsemll₃⟩ | ⟨hsemll₁, hsemll₂, hsemll₃⟩, ⟨⟨hsemlrll, hsemlrlr⟩, ⟨hsemlrrl, hsemlrrr⟩⟩ ⟩, hsemr ⟩
      <;> subst_vars
      . simp at H₇; subst_vars
        apply Exists.intro ((_, _), (_, (_, _)))
        rw [sigma_rw_simp]; dsimp
        refine ⟨⟨?_, ?_⟩, rfl⟩
        · rw [← H₅, List.map_append]
          have : ∀ a, x_new_fork ++ x_new_join2_l ++ (List.map Prod.fst x_new_muxF ++ a) = x_new_fork ++ x_new_join2_l ++ (List.map Prod.fst x_new_muxF) ++ a := by simp
          rw [this]; rfl
        · have : x_new_join2_r ++ List.map Prod.snd (x_new_muxF ++ [(vt, vv)]) = x_new_join2_r ++ List.map Prod.snd (x_new_muxF) ++ [vv] := by simp
          rw [this]
      . simp at H₆; subst_vars
        apply Exists.intro ((_, _), (_, (_, _)))
        rw [sigma_rw_simp]; dsimp
        refine ⟨⟨?_, ?_⟩, rfl⟩
        · rw[List.map_append]
          have : ∀ a, x_new_fork ++ x_new_join1_l ++ (List.map Prod.fst x_new_muxT ++ a) = x_new_fork ++ x_new_join1_l ++ (List.map Prod.fst x_new_muxT) ++ a := by simp
          rw [this]; rfl
        · rw[List.map_append]
          have : ∀ a, x_new_join1_r ++ (List.map Prod.snd x_new_muxT ++ a) = x_new_join1_r ++ (List.map Prod.snd x_new_muxT) ++ a := by simp
          rw [this]; rfl

theorem correct_threeway_merge'' {Tag T: Type _} [DecidableEq T]:
  rhsModule Tag T ⊑_{φ} lhsModule Tag T := by
  intro x y HPerm
  constructor
  . intro ident new_i v Hcontains Hsem
    rcases HPerm with ⟨ h₁, h₂, h₃, h₄, h₅, h₆, h₇ ⟩
    have Hkeys := AssocList.keysInMap Hcontains; clear Hcontains
    fin_cases Hkeys
    . simp [drunfold,drcompute,seval] at Hsem ⊢
      rw[sigma_rw_simp] at Hsem; simp at Hsem
      rcases new_i with ⟨x_new_fork, ⟨x_new_muxT, x_new_muxF, x_new_muxC⟩, ⟨x_new_join1_l, x_new_join1_r⟩, ⟨x_new_join2_l, x_new_join2_r⟩⟩
      subst_vars
      apply Exists.intro ((_, _), (_, (_, _)))
      rw [sigma_rw_simp]; dsimp
      constructor
      .  (repeat constructor) <;> rfl
      . constructor; constructor
        . constructor
        . simp at Hsem; rcases Hsem with ⟨ Hsem₁, Hsem₂⟩
          rcases x with ⟨x_fork, ⟨x_muxT, x_muxF, x_muxC⟩, ⟨x_join1_l, x_join1_r⟩, ⟨x_join2_l, x_join2_r⟩⟩
          simp at Hsem₂
          rcases Hsem₂ with ⟨ ⟨ _, _, _ ⟩ , ⟨ _, _ ⟩, _, _ ⟩
          constructor
          . simp
            subst_vars
            simp at *; assumption
          . and_intros <;> (try subst_vars) <;> (try simp[*]) <;> (try assumption)
    . simp [drunfold,drcompute,seval] at Hsem ⊢
      rw[sigma_rw_simp] at Hsem; simp at Hsem
      rcases new_i with ⟨x_new_fork, ⟨x_new_muxT, x_new_muxF, x_new_muxC⟩, ⟨x_new_join1_l, x_new_join1_r⟩, ⟨x_new_join2_l, x_new_join2_r⟩⟩
      subst_vars
      apply Exists.intro ((_, _), (_, (_, _)))
      rw [sigma_rw_simp]; dsimp
      constructor
      . (repeat constructor) <;> rfl
      . apply lhs_internal_correctness
        simp at Hsem; rcases Hsem with ⟨ Hsem₁, Hsem₂⟩
        rcases x with ⟨x_fork, ⟨x_muxT, x_muxF, x_muxC⟩, ⟨x_join1_l, x_join1_r⟩, ⟨x_join2_l, x_join2_r⟩⟩
        simp at Hsem₂
        rcases Hsem₂ with ⟨ ⟨ _, _, _ ⟩ , ⟨ _, _ ⟩, _, _ ⟩
        simp at Hsem₁
        rcases Hsem₁ with ⟨ ⟨ _, _, _ ⟩ , ⟨ _, _ ⟩, _, _ ⟩
        constructor <;> subst_vars <;> simp[*]
    . simp [drunfold,drcompute,seval] at Hsem ⊢
      rw[sigma_rw_simp] at Hsem; simp at Hsem
      rcases new_i with ⟨x_new_fork, ⟨x_new_muxT, x_new_muxF, x_new_muxC⟩, ⟨x_new_join1_l, x_new_join1_r⟩, ⟨x_new_join2_l, x_new_join2_r⟩⟩
      subst_vars
      apply Exists.intro ((_, _), (_, (_, _)))
      rw [sigma_rw_simp]; dsimp
      constructor
      . (repeat constructor) <;> rfl
      . apply lhs_internal_correctness
        simp at Hsem; rcases Hsem with ⟨ Hsem₁, Hsem₂⟩
        rcases x with ⟨x_fork, ⟨x_muxT, x_muxF, x_muxC⟩, ⟨x_join1_l, x_join1_r⟩, ⟨x_join2_l, x_join2_r⟩⟩
        simp at Hsem₂
        rcases Hsem₂ with ⟨ ⟨ _, _, _ ⟩ , ⟨ _, _ ⟩, _, _ ⟩
        simp at Hsem₁
        rcases Hsem₁ with ⟨ ⟨ _, _, _ ⟩ , ⟨ _, _ ⟩, _, _ ⟩
        constructor <;> subst_vars <;> simp[*]
    . simp [drunfold,drcompute,seval] at Hsem ⊢
      rw[sigma_rw_simp] at Hsem; simp at Hsem
      rcases new_i with ⟨x_new_fork, ⟨x_new_muxT, x_new_muxF, x_new_muxC⟩, ⟨x_new_join1_l, x_new_join1_r⟩, ⟨x_new_join2_l, x_new_join2_r⟩⟩
      subst_vars
      apply Exists.intro ((_, _), (_, (_, _)))
      rw [sigma_rw_simp]; dsimp
      constructor
      . (repeat constructor) <;> rfl
      . apply lhs_internal_correctness
        simp at Hsem; rcases Hsem with ⟨ Hsem₁, Hsem₂⟩
        rcases x with ⟨x_fork, ⟨x_muxT, x_muxF, x_muxC⟩, ⟨x_join1_l, x_join1_r⟩, ⟨x_join2_l, x_join2_r⟩⟩
        simp at Hsem₂
        rcases Hsem₂ with ⟨ ⟨ _, _, _ ⟩ , ⟨ _, _ ⟩, _, _ ⟩
        simp at Hsem₁
        rcases Hsem₁ with ⟨ ⟨ _, _, _ ⟩ , ⟨ _, _ ⟩, _, _ ⟩
        constructor <;> subst_vars <;> simp[*]



end DataflowRewriter.MuxTaggedRewrite
