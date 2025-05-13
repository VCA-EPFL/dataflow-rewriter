/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/
import Lean
import Init.Data.BitVec.Lemmas
import Qq

import DataflowRewriter.Module
import DataflowRewriter.Component
import DataflowRewriter.ModuleReduction
import DataflowRewriter.ExprLow
import DataflowRewriter.ExprLowLemmas

import DataflowRewriter.Examples.NoC.BasicLemmas
import DataflowRewriter.Examples.NoC.Perm
import DataflowRewriter.Examples.NoC.ComponentsImplementation.TwoXTwo

open Batteries (AssocList)

namespace DataflowRewriter.Examples.NoC.TwoXTwo

-- Useful lemmas ---------------------------------------------------------------

theorem perm_in_perm_l {α} {l1 l2 : List α} {v} {H : l1.Perm l2} (Hin : v ∈ l2 := by simp):
  ∃ i : Fin l1.length, l1[i] = v := by
    sorry

theorem perm_in_perm_r {α} {l1 l2 : List α} {v} {H : l1.Perm l2} (Hin : v ∈ l1 := by simpa) :
  ∃ i : Fin l2.length, l2[i] = v := by
    apply perm_in_perm_l
    · rw [List.perm_comm]
    · sorry

theorem getX_getY_correct {rId dst : RouterID} (Hx : getX rId = getX dst) (Hy : getY rId = getY dst) :
   dst = rId := by
    dsimp [getX] at Hx
    dsimp [getY] at Hy
    sorry -- Annoying

theorem arbiterXY_correct {rId dst : RouterID} :
  arbiterXY rId dst = DirLocal → dst = rId := by
    dsimp [arbiterXY]
    cases Heq : (getX rId == getX dst && getY rId == getY dst)
    · sorry -- Contradiction, a bit annoying
    · dsimp
      intros _
      simp only [Bool.and_eq_true, beq_iff_eq] at Heq
      obtain ⟨HeqX, HeqY⟩ := Heq
      apply getX_getY_correct HeqX HeqY

-- Lemmas for permutation using aesop ------------------------------------------

theorem perm_eraseIdx {α} {v} {l l1 l2 : List α} {idx : Fin l.length} (Heq : l[idx] = v := by simpa) :
  List.Perm l ([v] ++ l1 ++ l2) ↔ List.Perm (List.eraseIdx l idx) (l1 ++ l2) :=
  by sorry

theorem append_cons {α} {v} {l : List α} : v :: l = [v] ++ l := by rfl

-- Proof of correctness --------------------------------------------------------

instance : MatchInterface noc_lowM noc := by
  dsimp [noc_lowM, noc]
  solve_match_interface

def φ (I : noc_lowT) (S : nocT) : Prop :=
  List.Perm S (I.1 |> I.2.1.append |> I.2.2.1.append |> I.2.2.2.1.append)

theorem perm_in_perm_φ {I : noc_lowT} {S : nocT} {v} {Hφ : φ I S} :
  v ∈ (I.1 |> I.2.1.append |> I.2.2.1.append |> I.2.2.2.1.append)
  → ∃ i : Fin S.length, List.get S i = v := by
    apply perm_in_perm_l; exact Hφ

theorem noc_low_refines_initial :
  Module.refines_initial noc_lowM noc φ := by
    intros i Hi
    dsimp [noc_lowM] at Hi
    exists []
    simpa [φ, Hi, drcompute, drcomponents]

theorem noc_low_refines_φ : noc_lowM ⊑_{φ} noc := by
  intros i s H
  constructor
  · intros ident mid_i v Hrule
    case_transition Hcontains : (Module.inputs noc_lowM), ident,
     (PortMap.getIO_not_contained_false' Hrule)
    simp only [
      noc_lowM,
      AssocList.contains_eq, AssocList.toList,
      List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq
    ] at Hcontains
    rcases Hcontains with H | H | H | H
    <;> subst ident
    <;> dsimp [noc_lowM, drcompute] at Hrule v ⊢
    <;> unfold φ at *
    <;> dsimp only [List.append_eq] at *
    <;> exists (s ++ [v])
    <;> exists (s ++ [v])
    <;> and_intros
    <;> try rfl
    all_goals dsimp [drcomponents]
    all_goals try constructor; done
    all_goals repeat rw [and_assoc] at Hrule
    · obtain ⟨Hrule1, Hrule2⟩ := Hrule
      rw [Hrule1, ←Hrule2]
      repeat rw [←List.append_assoc] at *
      rwa [List.perm_append_right_iff (l := [v])]
    · obtain ⟨Hrule1, Hrule2, Hrule3⟩ := Hrule
      rw [←Hrule3, Hrule1, ←Hrule2]
      dr_perm_put_in_front [v]
      apply List.Perm.append_left
      dr_perm_put_in_front i.1
      dr_perm_put_in_front i.2.1
      dr_perm_put_in_front i.2.2.1
      dr_perm_put_in_front i.2.2.2.1
      assumption
    · obtain ⟨Hrule1, Hrule2, Hrule3, Hrule4⟩ := Hrule
      rw [Hrule1, ←Hrule2, ←Hrule3, ←Hrule4]
      dr_perm_put_in_front [v]
      apply List.Perm.append_left
      dr_perm_put_in_front i.1
      dr_perm_put_in_front i.2.1
      dr_perm_put_in_front i.2.2.1
      dr_perm_put_in_front i.2.2.2.1
      assumption
    · obtain ⟨Hrule1, Hrule2, Hrule3, Hrule4⟩ := Hrule
      rw [Hrule1, ←Hrule2, ←Hrule3, ←Hrule4]
      dr_perm_put_in_front [v]
      apply List.Perm.append_left
      dr_perm_put_in_front i.1
      dr_perm_put_in_front i.2.1
      dr_perm_put_in_front i.2.2.1
      dr_perm_put_in_front i.2.2.2.1
      assumption
  · intros ident mid_i v Hrule
    case_transition Hcontains : (Module.outputs noc_lowM), ident,
     (PortMap.getIO_not_contained_false' Hrule)
    simp only [
      noc_lowM,
      AssocList.contains_eq, AssocList.toList,
      List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq
    ] at Hcontains
    rcases Hcontains with H | H | H | H
    <;> subst ident
    <;> dsimp [noc_lowM, drcompute] at Hrule v ⊢
    <;> unfold φ at *
    <;> dsimp only [List.append_eq] at *
    <;> repeat rw [and_assoc] at Hrule
    -- TODO: In all of these cases, we need to remove v from s, some part is
    -- annoying to prove
    · obtain ⟨H1, H2, H3⟩ := Hrule
      rw [H1, H3] at H
      dsimp [arbiterXY, getX, getY] at H2
      rw [append_cons] at H
      repeat rw [←List.append_assoc]
      repeat rw [←List.append_assoc] at H
      obtain ⟨idx, Hidx⟩ := perm_in_perm_l (H := H) (v := v)
      exists List.eraseIdx s idx
      and_intros
      · rw [arbiterXY_correct H2]
      · exists idx; simpa [←Hidx]
      · rw [←perm_eraseIdx (v := v) (idx := idx)]
        sorry
    · obtain ⟨H1, H2, H3, H4⟩ := Hrule
      rw [H1, H3, H4] at H
      dsimp [List.append_eq] at H ⊢
      rw [append_cons] at H
      repeat rw [←List.append_assoc]
      repeat rw [←List.append_assoc] at H
      obtain ⟨idx, Hidx⟩ := perm_in_perm_l (H := H) (v := v)
      exists List.eraseIdx s idx
      and_intros
      · rw [arbiterXY_correct H2]
      · exists idx; simpa [←Hidx]
      · rw [←perm_eraseIdx (v := v) (idx := idx)]
        sorry
    · obtain ⟨H1, H2, H3, H4, H5⟩ := Hrule
      rw [H1, H3, H4, H5] at H
      dsimp [List.append_eq] at H ⊢
      rw [append_cons] at H
      repeat rw [←List.append_assoc]
      repeat rw [←List.append_assoc] at H
      obtain ⟨idx, Hidx⟩ := perm_in_perm_l (H := H) (v := v)
      exists List.eraseIdx s idx
      and_intros
      · rw [arbiterXY_correct H2]
      · exists idx; simpa [←Hidx]
      · rw [←perm_eraseIdx (v := v) (idx := idx)]
        sorry
    · obtain ⟨H1, H2, H3, H4, H5⟩ := Hrule
      rw [H1, H3, H4] at H
      rw [append_cons] at H
      repeat rw [←List.append_assoc]
      repeat rw [←List.append_assoc] at H
      obtain ⟨idx, Hidx⟩ := perm_in_perm_l (H := H) (v := v)
      exists List.eraseIdx s idx
      and_intros
      · rw [arbiterXY_correct H2]
      · exists idx; simpa [←Hidx]
      · rw [←perm_eraseIdx (v := v) (idx := idx)]
        sorry
  · intros rule mid_i H1 H2
    simp only [noc_lowM, List.mem_cons, List.not_mem_nil] at H1
    simp only [or_false, or_self_left] at H1
    rcases H1 with H1 | H1 | H1 | H1 | H1 | H1 | H1 | H1 | H1
    <;> subst rule
    <;> dsimp [drcomponents]
    <;> exists s
    <;> constructor
    <;> try (constructor; done)
    all_goals unfold φ at *
    all_goals obtain ⟨consumed_output, output, H⟩ := H2
    all_goals repeat rw [and_assoc] at H
    -- TODO: We need annoying permutations lemmas
    · obtain ⟨H1, H2, H3, H4, H5, H6, H7⟩ := H
      rw [H4, ←H5, ←H6, ←H7,]
      rw [H1, H3] at H
      dsimp at H ⊢
      -- ok
      sorry
    · obtain ⟨H1, H2, H3, H4, H5, H6, H7⟩ := H
      rw [H1, H3, H4, H5] at H
      rw [H6, ←H7]
      dsimp at H ⊢
      repeat rw [←List.append_assoc]
      repeat rw [←List.append_assoc] at H
      -- ok
      sorry
    · obtain ⟨H1, H2, H3, H4, H5, H6, H7, H8⟩ := H
      rw [H1, H3, H4] at H
      rw [H5, ←H6, ←H7, ←H8]
      dsimp at H ⊢
      repeat rw [←List.append_assoc]
      repeat rw [←List.append_assoc] at H
      -- ok
      sorry
    · obtain ⟨H1, H2, H3, H4, H5, H6, H7, H8⟩ := H
      rw [H1, H3, H4, H5] at H
      rw [H6, ←H7, ←H8]
      dsimp at H ⊢
      -- ok
      sorry
    · obtain ⟨H1, H2, H3, H4, H5, H6⟩ := H
      rw [H1, H3] at H
      rw [H4, ←H5, ←H6]
      dsimp at H ⊢
      simpa
    · obtain ⟨H1, H2, H3, H4, H5, H6⟩ := H
      rw [H1, H3, H4] at H
      rw [H5, ←H6]
      dsimp at H ⊢
      -- ok
      sorry
    · obtain ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9⟩ := H
      rw [H1, H3, H4, H5] at H
      rw [H6, ←H7, ←H8, ←H9]
      dsimp at H ⊢
      simpa
    · obtain ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9⟩ := H
      rw [H1, H3, H4, H5] at H
      rw [H6, ←H7, ←H8, ←H9]
      dsimp at H ⊢
      -- ok
      sorry

theorem noc_low_ϕ_indistinguishable :
  ∀ i s, φ i s → Module.indistinguishable noc_lowM noc i s := by
    intros i s H
    constructor
    <;> intros ident new_i v Hrule
    <;> dsimp [drcomponents, noc_lowM, List.range, List.range.loop, toString] at *
    · case_transition Hcontains : (Module.inputs noc_lowM), ident,
     (PortMap.getIO_not_contained_false' Hrule)
      simp only [
        noc_lowM,
        AssocList.contains_eq, AssocList.toList,
        List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq
      ] at Hcontains
      rcases Hcontains with Hident | Hident | Hident | Hident
      <;> subst ident
      <;> dsimp only [noc_lowM, drcompute] at Hrule v ⊢
      <;> exists s ++ [v]
      <;> simpa
    · case_transition Hcontains : (Module.outputs noc_lowM), ident,
     (PortMap.getIO_not_contained_false' Hrule)
      simp only [
        noc_lowM,
        AssocList.contains_eq, AssocList.toList,
        List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq
      ] at Hcontains
      rcases Hcontains with Hident | Hident | Hident | Hident
      <;> subst ident
      <;> dsimp only [noc_lowM, drcompute] at Hrule v ⊢
      <;> unfold φ at H
      <;> repeat rw [and_assoc] at Hrule
      · obtain ⟨Hrule1, Hrule2, Hrule3⟩ := Hrule
        rw [Hrule1] at H
        obtain ⟨i, Hi⟩ := perm_in_perm_l (H := H) (v := v)
        exists List.eraseIdx s ↑i
        and_intros
        · rw [arbiterXY_correct Hrule2]
        · exists i; rw [←Hi]; simpa
      · obtain ⟨Hrule1, Hrule2, Hrule3, Hrule4⟩ := Hrule
        rw [Hrule1] at H
        obtain ⟨i, Hi⟩ := perm_in_perm_l (H := H) (v := v)
        exists List.eraseIdx s ↑i
        and_intros
        · rw [arbiterXY_correct Hrule2]
        · exists i; rw [←Hi]; simpa
      · obtain ⟨Hrule1, Hrule2, Hrule3, Hrule4, Hrule5⟩ := Hrule
        rw [Hrule1] at H
        obtain ⟨i, Hi⟩ := perm_in_perm_l (H := H) (v := v)
        exists List.eraseIdx s ↑i
        and_intros
        · rw [arbiterXY_correct Hrule2]
        · exists i; rw [←Hi]; simpa
      · obtain ⟨Hrule1, Hrule2, Hrule3, Hrule4, Hrule5⟩ := Hrule
        rw [Hrule1] at H
        obtain ⟨i, Hi⟩ := perm_in_perm_l (H := H) (v := v)
        exists List.eraseIdx s ↑i
        and_intros
        · rw [arbiterXY_correct Hrule2]
        · exists i; rw [←Hi]; simpa

theorem noc_low_correct : noc_lowM ⊑ noc := by
  apply (
    Module.refines_φ_refines
      noc_low_ϕ_indistinguishable
      noc_low_refines_initial
      noc_low_refines_φ
  )

end DataflowRewriter.Examples.NoC.TwoXTwo
