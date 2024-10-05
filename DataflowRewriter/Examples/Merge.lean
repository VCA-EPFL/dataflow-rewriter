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
def threemerge' (T:Type) : Module (List T) := by precompute threemerge T

opaque threemerge_threemerge' T : threemerge T = threemerge' T := by rfl

@[simp]
def mergeLow : ExprLow Nat :=
  let merge1 := .base 1 0
  let merge2 := .base 2 0
  .product merge1 merge2
  |> .connect ⟨1, 0⟩ ⟨2, 0⟩
  |> .input ⟨1, 0⟩ 0
  |> .input ⟨1, 1⟩ 1
  |> .input ⟨2, 1⟩ 2
  |> .output ⟨2, 0⟩ 0

def merge_sem (T: Type _) :=
  match build_module' mergeLow ([(0, ⟨List T, merge T⟩)].toAssocList) with
  | some x => x
  | none => ⟨Unit, Module.empty⟩

seal List.get List.remove in
def merge_sem' (T:Type) : ((X:Type) × Module X) := by precompute merge_sem T

attribute [dmod] Batteries.AssocList.find? BEq.beq

opaque merge_sem_merge_sem' T : merge_sem T = merge_sem' T := by rfl

theorem getIO_none {S} (m : PortMap Ident ((T : Type) × (S → T → S → Prop))) (ident : Ident) :
  m.find? ↑ident = none ->
  m.getIO ident = ⟨ PUnit, λ _ _ _ => True ⟩ := by
  intros H; rw [Batteries.AssocList.find?_eq] at H
  dsimp at H; simp [H]

theorem getIO_some {S} (m : PortMap Ident ((T : Type) × (S → T → S → Prop))) (ident : Ident) t :
  m.find? ↑ident = some t ->
  m.getIO ident = t := by
  intros H; rw [Batteries.AssocList.find?_eq] at H
  dsimp at H; simp [H]

theorem AssocList_contains_none {S : Type _} (m : PortMap Ident ((T : Type) × (S → T → S → Prop))) ident :
  ¬ m.contains ident ->
  m.find? ident = none := by
  intros H; rw [Batteries.AssocList.contains_eq] at H
  rw [Batteries.AssocList.find?_eq]
  rw [Option.map_eq_none', List.find?_eq_none]; intros x H
  rcases x with ⟨ a, ⟨ b, c ⟩⟩
  simp at *; unfold Not; intros; apply H
  subst_vars; assumption

theorem AssocList_contains_some {S : Type _} (m : PortMap Ident ((T : Type) × (S → T → S → Prop))) ident :
  m.contains ident ->
  (m.find? ident).isSome := by
  intros H; rw [Batteries.AssocList.contains_eq] at H; simp at H; rcases H with ⟨ a, b, H ⟩
  simp [*]; tauto

theorem inputs_match {S S'} (A : Module S) (B : Module S') :
  (A.inputs.toList.map (·.fst)).Perm (B.inputs.toList.map (·.fst)) →
  ∀ (ident : Ident), (A.inputs.getIO ident).1 = (B.inputs.getIO ident).1 := by stop
  intro HPerm ident; by_cases h : (A.inputs.contains ↑ident)
  · apply AssocList_contains_some at h
    rw [Option.isSome_iff_exists] at h; rcases h with ⟨ a, h ⟩
    rw [getIO_some _ _ _ h]
  sorry

theorem outputs_match {S S'} (A : Module S) (B : Module S') :
  (A.outputs.toList.map (·.fst)).Perm (B.outputs.toList.map (·.fst)) →
  ∀ (ident : Ident), (A.outputs.getIO ident).1 = (B.outputs.getIO ident).1 := by sorry

theorem interface_match T : matching_interface ((merge_sem' T).snd) (threemerge' T) := by
  constructor
  · apply inputs_match; solve_by_elim only [List.Perm.swap, List.Perm.trans]
  · apply outputs_match; rfl

instance matching_three {T} : MatchingModules (List T × List T) (List T) Ident where
  imod := (merge_sem' T).snd
  smod := threemerge' T
  matching := interface_match T

theorem keysInMap'' {α β} [DecidableEq α] (m : AssocList α β) : ∀ k, m.contains k → k ∈ m.keysList := by
  unfold Batteries.AssocList.contains Batteries.AssocList.keysList
  intro k Hk; simp at Hk; simp [*]

theorem sigma_rw {S T : Type _} {m m' : Σ (y : Type _), S → y → T → Prop} {x : S} {y : T} {v : m.fst}
        (h : m = m' := by reduce; rfl) :
  m.snd x v y ↔ m'.snd x (h ▸ v) y := by
  constructor <;> (intros; subst h; assumption)

theorem correct_threeway_merge {T: Type _} [DecidableEq T]:
    @refines _ _ _ _ _ (@matching_three T) (fun (x : List T × List T) y => (x.1 ++ x.2).Perm y) := by
      intro ⟨ x1, x2 ⟩ y HPerm indis
      apply comp_refines.mk
      . intro ident ⟨x'1, x'2⟩ v Hcontains Himod
        have := keysInMap'' _ _ Hcontains
        fin_cases this
        · dsimp at *
          simp [dmod] at Himod
          rw [sigma_rw] at Himod
          dsimp at Himod
          let ⟨ Hl, Hr ⟩ := Himod; clear Himod; subst_vars
          constructor; constructor; and_intros
          · rfl
          · apply existSR.done
          · exact List.Perm.symm (List.perm_cons_append_cons v (List.Perm.symm HPerm))
          · constructor
            · intro ident' new_i v_1 Hcontains Hrule
              have := keysInMap'' _ _ Hcontains
              fin_cases this <;> (simp [dmod]; constructor; rw [sigma_rw])
            · intro ident' ⟨ new_i_1, new_i_2 ⟩ v_1 Hcontains HVal
              have := keysInMap'' _ _ Hcontains; fin_cases this
              let ⟨ ⟨ i, HVall, temp ⟩, HValr ⟩ := HVal; clear HVal
              subst_vars; simp [dmod];
              generalize h : (v :: x2).get i = y'
              have Ht : ∃ i, (v :: x2).get i = y' := by exists i
              rw [← List.mem_iff_get] at Ht
              have He := List.Perm.symm (List.perm_cons_append_cons v (List.Perm.symm HPerm))
              have Hiff := List.Perm.mem_iff (a := y') He
              have Ht' : y' ∈ v :: y := by rw [← Hiff]; simp; cases Ht <;> tauto
              rw [List.mem_iff_get] at Ht'
              rcases Ht' with ⟨ i', Ht'r ⟩
              constructor; rw [sigma_rw]; dsimp; exists i'; and_intros; rfl
              subst_vars; symm; assumption
        · dsimp at *
          simp [dmod] at Himod
          rw [sigma_rw] at Himod
          dsimp at Himod
          let ⟨ Hl, Hr ⟩ := Himod; clear Himod; subst_vars
          constructor; constructor; and_intros
          · rfl
          · apply existSR.done
          · simp [*]
          · constructor
            · intro ident' new_i v_1 Hcontains Hrule
              have := keysInMap'' _ _ Hcontains
              fin_cases this <;> (simp [dmod]; constructor; rw [sigma_rw])
            · intro ident' ⟨ new_i_1, new_i_2 ⟩ v_1 Hcontains HVal
              have := keysInMap'' _ _ Hcontains; fin_cases this
              let ⟨ ⟨ i, HVall, temp ⟩, HValr ⟩ := HVal; clear HVal
              subst_vars; simp [dmod];
              generalize h : x'2.get i = y'
              have Ht : ∃ i, x'2.get i = y' := by exists i
              rw [← List.mem_iff_get] at Ht; reduce at v
              have He : (v :: x1 ++ x'2).Perm (v :: y) := by simp [*]
              have Hiff := List.Perm.mem_iff (a := y') He
              have Ht' : y' ∈ v :: y := by rw [← Hiff]; simp; cases Ht <;> tauto
              rw [List.mem_iff_get] at Ht'
              rcases Ht' with ⟨ i', Ht'r ⟩
              constructor; rw [sigma_rw]; dsimp; exists i'; and_intros; rfl
              subst_vars; symm; assumption
        · dsimp at *
          simp [dmod] at Himod
          rw [sigma_rw] at Himod
          dsimp at Himod
          let ⟨ Hl, Hr ⟩ := Himod; clear Himod; subst_vars
          constructor; constructor; and_intros
          · rfl
          · apply existSR.done
          · simp [*]
          · constructor
            · intro ident' new_i v_1 Hcontains Hrule
              have := keysInMap'' _ _ Hcontains
              fin_cases this <;> (simp [dmod]; constructor; rw [sigma_rw])
            · intro ident' ⟨ new_i_1, new_i_2 ⟩ v_1 Hcontains HVal
              have := keysInMap'' _ _ Hcontains; fin_cases this
              let ⟨ ⟨ i, HVall, temp ⟩, HValr ⟩ := HVal; clear HVal
              subst_vars; simp [dmod];
              generalize h : x'2.get i = y'
              have Ht : ∃ i, x'2.get i = y' := by exists i
              rw [← List.mem_iff_get] at Ht; reduce at v
              have He : (v :: x1 ++ x'2).Perm (v :: y) := by simp [*]
              have Hiff := List.Perm.mem_iff (a := y') He
              have Ht' : y' ∈ v :: y := by rw [← Hiff]; simp; cases Ht <;> tauto
              rw [List.mem_iff_get] at Ht'
              rcases Ht' with ⟨ i', Ht'r ⟩
              constructor; rw [sigma_rw]; dsimp; exists i'; and_intros; rfl
              subst_vars; symm; assumption
      · intro ident mid_i v Hcontains Hi
        have := keysInMap'' _ _ Hcontains
        fin_cases this
        rcases Hi with ⟨ ⟨ i, Hil ⟩, Hir ⟩
        reduce at *
        rcases Hil with ⟨ Hill, Hilr ⟩
        subst v; subst x1
        generalize Hx2get : x2.get i = v'
        have Hx2in : v' ∈ x2 := by rw [List.mem_iff_get]; tauto
        have He := HPerm
        have Hiff := List.Perm.mem_iff (a := v') HPerm
        have Hyin : v' ∈ y := by rw [← Hiff]; simp; tauto
        rw [List.mem_iff_get] at Hyin
        rcases Hyin with ⟨ i', Hyget ⟩
        have HerasePerm : (mid_i.1.append mid_i.2).Perm (y.eraseIdx i'.1) := by
          simp [Hill]
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
        · exists i'; and_intros; rfl; tauto
        · apply existSR.done
        · assumption
        · constructor <;> dsimp only
          · intro ident' new_i v_1 Hcontains Hrule
            have := keysInMap'' _ _ Hcontains
            fin_cases this <;> (simp [dmod]; constructor; rw [sigma_rw])
          · intros ident' new_i v_1 Hcontains HVal
            have := keysInMap'' _ _ Hcontains
            fin_cases this
            reduce at *
            rcases HVal with ⟨ ⟨ i'', HVall, temp ⟩, HValr ⟩
            subst v'; subst v_1
            dsimp at *
            have : mid_i.2[i''] ∈ (x2.eraseIdx i.1) := by
              simp [Hill]; apply List.getElem_mem
            have : mid_i.2[i''] ∈ (mid_i.1 ++ x2.eraseIdx i.1) := by
              rw [List.mem_eraseIdx_iff_getElem] at this; simp; right
              simp at *; simp [Hill]; apply List.getElem_mem
            have HPermIn : mid_i.2[i''] ∈ y.eraseIdx i' := by
              rw [List.Perm.mem_iff]; assumption; symm
              rw [←Hill]; assumption
            rw [List.mem_iff_getElem] at HPermIn
            rcases HPermIn with ⟨ Ha, Hb, Hc ⟩
            constructor; exists ⟨ Ha, Hb ⟩; tauto
      · intro ident mid_i Hcontains Hv
        fin_cases Hcontains; have Hv' := Hv rfl; clear Hv
        reduce at *
        rcases Hv' with ⟨ ⟨ la1, la2 ⟩, lb, Hv' ⟩; reduce at *; 
        rcases Hv' with  ⟨ ⟨ ⟨ i, H2, H3 ⟩, Hx3 ⟩, Hx2, H4 ⟩
        subst lb; subst la1; subst la2
        constructor; and_intros
        · apply existSR.done
        · rw [Hx2,← H4]
          have : ((x1.eraseIdx ↑i).append (x1.get i :: x2)) = ((x1.eraseIdx ↑i) ++ (x1.get i :: x2)) := by rfl
          rw [this]; clear this
          rw [←List.eraseIdx_append_of_lt_length] <;> [skip; apply i.isLt]
          dsimp only;
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
        · constructor
          · intros ident' new_i v_1 Hcontains Hrule
            have := keysInMap'' _ _ Hcontains
            fin_cases this <;> (simp [dmod]; constructor; rw [sigma_rw])
          · intros ident' new_i v_1 Hcontains HVal
            have := keysInMap'' _ _ Hcontains
            fin_cases this
            reduce at *
            rcases HVal with ⟨ ⟨ i', _, temp ⟩, _ ⟩
            subst v_1
            generalize h : mid_i.2.get i' = y'
            have Ht : ∃ i', mid_i.2.get i' = y' := by exists i'
            rw [← List.mem_iff_get] at Ht
            have Hiff := List.Perm.mem_iff (a := y') HPerm
            have Ht'' : y' ∈ x1.get i :: x2 := by rw [←Hx2]; assumption
            simp at Ht''; rcases Ht'' with (Ht'' | Ht'')
            · have Ht' : y' ∈ y := by
                rw [List.Perm.mem_iff]; rotate_left; rewrite [List.perm_comm]; assumption; subst y'
                rw [Ht'']; simp; left; apply List.getElem_mem
              dsimp; apply List.getElem_of_mem at Ht'; rcases Ht' with ⟨ Ha, Hb, Hc ⟩
              constructor; exists ⟨ Ha, Hb ⟩; and_intros; rfl; symm; assumption
            · have Ht' : y' ∈ y := by
                rw [List.Perm.mem_iff]; rotate_left; rewrite [List.perm_comm]; assumption; subst y'
                simp; tauto
              dsimp; apply List.getElem_of_mem at Ht'; rcases Ht' with ⟨ Ha, Hb, Hc ⟩
              constructor; exists ⟨ Ha, Hb ⟩; and_intros; rfl; symm; assumption

/--
info: 'DataflowRewriter.correct_threeway_merge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms correct_threeway_merge

end DataflowRewriter
