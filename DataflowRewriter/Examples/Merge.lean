/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Leanses
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

open Batteries (AssocList)

open Lean hiding AssocList
open Meta Elab

namespace DataflowRewriter

abbrev Ident := Nat

elab "precompute " t:term : tactic => Tactic.withMainContext do
  let expr ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsUsingDefault
  let expr ← Lean.instantiateMVars expr
  let expr ←
    -- withTransparency .all <|
      reallyReduce (skipArgs := false) (skipTypes := false) expr
  (← Tactic.getMainGoal).assign expr

def threemerge T : Module (List T):=
  { inputs := [(0, ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩),
               (1, ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩),
               (2, ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩)].toAssocList,
    outputs := [(0, ⟨ T, λ oldList oldElement newList => ∃ i, newList = oldList.remove i ∧ oldElement = oldList.get i ⟩)].toAssocList,
    internals := []
  }

seal _root_.List.get _root_.List.remove in
@[drunfold] def threemerge' (T:Type) : Module (List T) := by precompute threemerge T

opaque threemerge_threemerge' T : threemerge T = threemerge' T := by rfl

@[drunfold] def mergeLow : ExprLow Nat :=
  let merge1 := .base 1 0
  let merge2 := .base 2 0
  .product merge1 merge2
  |> .connect ⟨1, 0⟩ ⟨2, 0⟩
  |> .input ⟨1, 0⟩ 0
  |> .input ⟨1, 1⟩ 1
  |> .input ⟨2, 1⟩ 2
  |> .output ⟨2, 0⟩ 0

def merge_sem (T: Type _) :=
  mergeLow.build_module [(0, ⟨List T, Module.merge T⟩)].toAssocList

seal List.get List.remove in
@[drunfold] def merge_sem' (T:Type) : ((X:Type) × Module X) := by precompute merge_sem T

attribute [dmod] Batteries.AssocList.find? BEq.beq

opaque merge_sem_merge_sem' T : merge_sem T = merge_sem' T := by rfl

theorem AssocList_contains_none {S : Type _}
    (m : PortMap Ident ((T : Type) × (S → T → S → Prop))) ident :
    ¬ m.contains ident →
    m.find? ident = none := by
  intros H; rw [Batteries.AssocList.contains_eq] at H
  rw [Batteries.AssocList.find?_eq]
  rw [Option.map_eq_none', List.find?_eq_none]; intros x H
  rcases x with ⟨ a, ⟨ b, c ⟩⟩
  simp at *; unfold Not; intros; apply H
  subst_vars; assumption

theorem AssocList_contains_some {S : Type _}
    (m : PortMap Ident ((T : Type) × (S → T → S → Prop))) ident :
    m.contains ident →
    (m.find? ident).isSome := by
  intros H; rw [Batteries.AssocList.contains_eq] at H; simp at H; rcases H with ⟨ a, b, H ⟩
  simp [*]; tauto

@[simp] theorem any_map {α β} {f : α → β} {l : List α} {p : β → Bool} : (l.map f).any p = l.any (p ∘ f) := by
  induction l with simp | cons _ _ ih => rw [ih]

-- theorem inputs_match {α β} [DecidableEq α] (A B : List (α × β)) i :
--     A.Perm B →
--     (A.map Prod.fst).Nodup →
--     A.find? (i == ·.1) = B.find? (i == ·.1) := by
--   intro HPerm HNodup; have HNodup2 := List.Nodup.perm HNodup <| List.Perm.map Prod.fst HPerm
--   have hrw : ((i == ·.1) : (α × β → Bool)) = ((i == ·) ∘ Prod.fst) := by rfl
--   rw [hrw]
--   sorry

-- theorem inputs_match {α} [DecidableEq α] {γ : Type _ → Type _}
--     (A B : AssocList α (Σ β, γ β)) :
--     A.keysList.Nodup →
--     (A.toList.map (fun x => (x.1, x.2.1))).Perm (B.toList.map (fun x => (x.1, x.2.1))) →
--     ∀ (ident : α), (A.find? ident).map (·.fst) = (B.find? ident).map (·.fst) := by
--   intro HANoDup HPerm ident;
--   have Hmap := List.Perm.map (fun x => x.1) HPerm
--   rw [List.map_map] at Hmap; rw [List.map_map] at Hmap; reduce at Hmap
--   have HBNoDup := List.Nodup.perm HANoDup Hmap
--   have Hallin := (List.perm_ext_iff_of_nodup HANoDup HBNoDup).mp Hmap
--   simp only [AssocList.keysList, Batteries.AssocList.find?_eq] at *
--   specialize Hallin ident
--   by_cases h : (A.contains ↑ident)
--   · simp only [Batteries.AssocList.contains_eq] at *
--     have Hfun : (fun x => ident == x.1) = (((ident == ·) ∘ (·.fst)) : (α × (Σ β, γ β)) → Bool) := rfl
--     have hrw : (fun (x: (α × (Σ β, γ β))) => x.1 == ident) = (fun x => ident == x.1) := by
--       ext x; simp; constructor <;> (intros; subst ident; rfl)
--     rw [hrw,Hfun,←any_map,List.any_beq] at h; clear Hfun
--     have h2 := Hallin.mp h
--     simp only [AssocList.keysList, Batteries.AssocList.contains_eq, Batteries.AssocList.find?_eq, List.any_eq_true, List.find?_isSome] at *


-- theorem outputs_match {S S'} (A : Module S) (B : Module S') :
--   A.inputs.keysList.Nodup →
--   B.inputs.keysList.Nodup →
--   (A.outputs.toList.map (·.fst)).Perm (B.outputs.toList.map (·.fst)) →
--   ∀ (ident : Ident), (A.outputs.getIO ident).1 = (B.outputs.getIO ident).1 := by
--   intro HANoDup HBNoDup HPerm ident

-- theorem interface_match T : matching_interface ((merge_sem' T).snd) (threemerge' T) := by
--   constructor
--   · apply inputs_match; solve_by_elim only [List.Perm.swap, List.Perm.trans]
--   · apply outputs_match; rfl

theorem keysInMap {α β} [DecidableEq α] {m : AssocList α β} {k} : m.contains k → k ∈ m.keysList := by
  unfold Batteries.AssocList.contains Batteries.AssocList.keysList
  intro Hk; simp at Hk; simp [*]

theorem keysNotInMap {α β} [DecidableEq α] {m : AssocList α β} {k} : ¬ m.contains k → k ∉ m.keysList := by
  unfold Batteries.AssocList.contains Batteries.AssocList.keysList
  intro Hk; simp at Hk; simp [*]

instance {T} : MatchInterface (merge_sem' T).snd (threemerge' T) where
  input_types := by
    intro ident;
    by_cases h : (Batteries.AssocList.contains ↑ident (merge_sem' T).snd.inputs)
    · have h' := keysInMap h; fin_cases h' <;> rfl
    · have h' := keysNotInMap h; dsimp [drunfold, AssocList.keysList] at h' ⊢
      simp at h'; let ⟨ ha, hb, hc ⟩ := h'; clear h'
      simp only [Batteries.AssocList.find?_eq, Batteries.AssocList.toList]
      simp (discharger := simp; omega) [List.find?_cons_of_neg]
  output_types := by
    intro ident;
    by_cases h : (Batteries.AssocList.contains ↑ident (merge_sem' T).snd.outputs)
    · have h' := keysInMap h; fin_cases h' <;> rfl
    · have h' := keysNotInMap h; dsimp [drunfold, AssocList.keysList] at h' ⊢
      simp at h'
      simp only [Batteries.AssocList.find?_eq, Batteries.AssocList.toList]
      simp (discharger := simp; omega) [List.find?_cons_of_neg]

theorem sigma_rw {S T : Type _} {m m' : Σ (y : Type _), S → y → T → Prop} {x : S} {y : T} {v : m.fst}
        (h : m = m' := by reduce; rfl) :
  m.snd x v y ↔ m'.snd x (h ▸ v) y := by
  constructor <;> (intros; subst h; assumption)

def φ {T} (x : List T × List T) (y : List T) := (x.1 ++ x.2).Perm y

theorem φ_indistinguishable {T} :
  ∀ x y, φ x y → indistinguishable (merge_sem' T).snd (threemerge' T) x y := by
  unfold φ; intro x y H
  constructor <;> intro ident new_i v Hcontains Hsem
  · have Hkeys := keysInMap Hcontains; clear Hcontains
    fin_cases Hkeys <;> (constructor; rfl)
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

theorem correct_threeway_merge' {T: Type _} [DecidableEq T]:
    (merge_sem' T).snd ⊑_{φ} threemerge' T := by
      intro ⟨ x1, x2 ⟩ y HPerm
      apply comp_refines.mk
      . intro ident ⟨x'1, x'2⟩ v Hcontains Himod
        have := keysInMap Hcontains
        fin_cases this
        · dsimp at *
          rw [sigma_rw] at Himod
          dsimp at Himod
          let ⟨ Hl, Hr ⟩ := Himod; clear Himod; subst_vars
          have Hφ : φ (x'1, v :: x2) (v :: y) :=
            List.Perm.symm (List.perm_cons_append_cons v (List.Perm.symm HPerm))
          constructor; constructor; and_intros
          all_goals first | rfl | apply existSR.done | assumption
        · dsimp at *
          rw [sigma_rw] at Himod
          dsimp at Himod
          let ⟨ Hl, Hr ⟩ := Himod; clear Himod; subst_vars
          have Hφ : φ (v :: x1, x'2) (v :: y) := by
            simp [*, φ] at HPerm ⊢; assumption
          constructor; constructor; and_intros
          all_goals first | rfl | apply existSR.done | assumption
        · dsimp at *
          rw [sigma_rw] at Himod
          dsimp at Himod
          let ⟨ Hl, Hr ⟩ := Himod; clear Himod; subst_vars
          have Hφ : φ (v :: x1, x'2) (v :: y) := by
            simp [*, φ] at HPerm ⊢; assumption
          constructor; constructor; and_intros
          all_goals first | rfl | apply existSR.done | assumption
      · intro ident mid_i v Hcontains Hi
        have := keysInMap Hcontains
        fin_cases this
        rcases Hi with ⟨ ⟨ i, Hil ⟩, Hir ⟩
        rcases Hil with ⟨ Hill, Hilr ⟩
        dsimp at *
        subst v; subst x1
        generalize Hx2get : x2.get i = v'
        have Hx2in : v' ∈ x2 := by rw [List.mem_iff_get]; tauto
        have He := HPerm
        have Hiff := List.Perm.mem_iff (a := v') HPerm
        have Hyin : v' ∈ y := by rw [← Hiff]; simp; tauto
        rw [List.mem_iff_get] at Hyin
        rcases Hyin with ⟨ i', Hyget ⟩
        have HerasePerm : φ mid_i (y.eraseIdx i'.1) := by
          simp [φ, Hill]
          trans; apply List.perm_append_comm
          rw [←List.eraseIdx_append_of_lt_length] <;> [skip; apply i.isLt]
          trans ((x2 ++ mid_i.1).erase x2[i])
          have H2 : x2[i] = (x2 ++ mid_i.1)[i] := by
            symm; apply List.getElem_append_left
          rw [H2]; symm; apply List.erase_get
          symm; trans; symm; apply List.erase_get
          rw [Hyget]; simp at Hx2get; simp; rw [Hx2get]
          apply List.perm_erase; symm
          symm; trans; symm; assumption
          apply List.perm_append_comm
        constructor; constructor; and_intros
        · exists i'; and_intros; rfl; simp_all
        · apply existSR.done
        · assumption
      · intro ident mid_i Hcontains Hv
        fin_cases Hcontains; have Hv' := Hv rfl; clear Hv
        reduce at *
        rcases Hv' with ⟨ ⟨ la1, la2 ⟩, lb, Hv' ⟩; reduce at *;
        rcases Hv' with  ⟨ ⟨ ⟨ i, H2, H3 ⟩, Hx3 ⟩, Hx2, H4 ⟩
        subst lb; subst la1; subst la2
        have HerasePerm : φ mid_i y := by
          simp [φ, Hx2,← H4]
          rw [←List.eraseIdx_append_of_lt_length] <;> [skip; apply i.isLt]
          trans ((x1 ++ x1[i] :: x2).erase x1[i])
          rw [List.perm_comm]
          have : x1[↑i] = x1.get i := by simp
          simp [*] at *
          have H : x1[↑i] = (x1 ++ x1[↑i] :: x2)[↑i] := by
            symm; apply List.getElem_append_left
          dsimp at *; conv => arg 1; arg 2; rw [H]
          apply List.erase_get
          trans ((x1[i] :: (x1 ++ x2)).erase x1[i])
          apply List.perm_erase; simp
          rw [List.erase_cons_head]; assumption
        constructor; and_intros
        all_goals first | rfl | apply existSR.done | assumption

theorem correct_threeway_merge {T: Type _} [DecidableEq T] :
    (merge_sem' T).snd ⊑ threemerge' T :=
  refines_φ_refines (merge_sem' T).snd (threemerge' T) φ_indistinguishable correct_threeway_merge'

/--
info: 'DataflowRewriter.correct_threeway_merge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms correct_threeway_merge

end DataflowRewriter
