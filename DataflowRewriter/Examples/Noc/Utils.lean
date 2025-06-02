/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

-- A bunch of random stuff which doesn't quite fit with the rest

import DataflowRewriter.Module
import DataflowRewriter.Component

open Batteries (AssocList)

namespace DataflowRewriter.Noc

  @[simp] abbrev typeOf {α} (_ : α) := α

  theorem in_list_idx {α} {l : List α} {x : α} (H : x ∈ l) :
    ∃ i : Fin (List.length l), l[i] = x := by
      induction l with
      | nil => contradiction
      | cons hd tl HR =>
        rw [List.mem_cons] at H
        cases H <;> rename_i H
        · rw [H]; apply Exists.intro (Fin.mk 0 (by simpa)); simpa
        · obtain ⟨i, Hi'⟩ := HR H; exists (Fin.mk (i + 1) (by simpa))

  def fin_range (sz : Nat) : List (Fin sz) :=
    List.replicate sz 0
    |>.mapFinIdx (λ i _ h => Fin.mk i (by rwa [List.length_replicate] at h))

  theorem fin_in_fin_range (sz : Nat) (i : Fin sz) : i ∈ fin_range sz := by
    simp only [fin_range, List.mem_mapFinIdx, List.length_replicate]
    exists i.toNat, i.isLt

  theorem mapFinIdx_length {α β} (l : List α) (f : (i : Nat) → α → (h : i < l.length) → β) :
    (List.mapFinIdx l f).length = l.length := by
      simpa

  theorem mapFinIdx_get {α β} (l : List α) (f : (i : Nat) → α → (h : i < l.length) → β) (i : Fin (List.mapFinIdx l f).length) :
    (List.mapFinIdx l f).get i = f i l[i] (by rw [← mapFinIdx_length l f]; exact i.isLt) := by
      simpa

  -- RelIO ---------------------------------------------------------------------

  @[simp] abbrev RelIO (S : Type) := Σ T : Type, S → T → S → Prop

  def RelIO.liftFinf {α : Type _} (n : Nat) (f : Fin n → α) : PortMap Nat α :=
    fin_range n |>.map (λ i => ⟨↑i.toNat, f i⟩) |>.toAssocList

  theorem RelIO.liftFinf_in {S} {ident : InternalPort Nat} {n : Nat} {f : Fin n → RelIO S}:
    AssocList.contains ident (RelIO.liftFinf n f) = true
    → ∃ i : Fin n, ident = i := by
        dsimp [liftFinf, fin_range]
        simp only [
          AssocList.contains_eq, List.toList_toAssocList, List.any_map,
          List.any_eq_true, List.mem_mapFinIdx, List.length_replicate,
          Function.comp_apply, beq_iff_eq, forall_exists_index, and_imp
        ]
        intros x1 x2 H1 H2 H3
        subst ident
        exists x1

  theorem RelIO.liftFinf_get {S} {n : Nat} {i : Fin n} {f : Fin n → RelIO S}:
    (RelIO.liftFinf n f).getIO i = f i := by sorry

  theorem RelIO_mapVal {α β} {n : Nat} {f : Fin n → α} {g : α → β} :
    AssocList.mapVal (λ _ => g) (RelIO.liftFinf n f) = RelIO.liftFinf n (λ i => g (f i)) :=
    by
      dsimp [RelIO.liftFinf, fin_range]
      rw [AssocList.mapVal_map_toAssocList]

  -- RelInt --------------------------------------------------------------------

  @[simp] abbrev RelInt (S : Type) := S → S → Prop

  def RelInt.liftFinf {S : Type} (n : Nat) (f : Fin n → List (RelInt S)) : List (RelInt S) :=
    fin_range n |>.map f |>.flatten

  theorem RelInt.liftFinf_in {S} {rule : RelInt S} {n : Nat} {f : Fin n → List (RelInt S)}:
    -- TODO: This is probably an equivalence too
    rule ∈ (RelInt.liftFinf n f)
    → ∃ (i : Fin n) (j : Fin (List.length (f i))), rule = (f i).get j := by sorry

  theorem RelInt.liftFinf_in' {S} {rule : RelInt S} {n : Nat} {f : Fin n → List (RelInt S)}:
    (∃ (i : Fin n) (j : Fin (List.length (f i))), rule = (f i).get j) →
    rule ∈ (RelInt.liftFinf n f) := by
      intro ⟨i, j, Hij⟩
      rw [Hij]
      unfold liftFinf
      simp only [RelInt, List.get_eq_getElem, List.mem_flatten, List.mem_map]
      exists (f i)
      and_intros
      · exists i; and_intros
        · apply fin_in_fin_range
        · rfl
      · simpa

  -- Some stuff about permutations ---------------------------------------------

  variable {α} {n : Nat}

  theorem vec_set_concat_perm {v : Vector (List α) n} {idx : Fin n} {l : List α} {elt : α} :
    v.toList.flatten.Perm l →
    (v.set idx (v[idx] ++ [elt])).toList.flatten.Perm (l ++ [elt]) := by
      sorry

  theorem vec_set_concat_in {v : Vector (List α) n} {idx : Fin n} {l : List α} {elt : α} :
    v.toList.flatten ⊆ l →
    (v.set idx (v[idx] ++ [elt])).toList.flatten ⊆ (l ++ [elt]) := by
      intros H x Hx
      simp only [Fin.getElem_fin, List.mem_flatten, Vector.mem_toList_iff] at Hx
      obtain ⟨l', Hl1, Hl2⟩ := Hx
      sorry

  theorem vec_set_subset_in {v : Vector (List α) n} {idx : Fin n} {l : List α} {elt : α} :
    (v.set idx (elt :: v[↑idx])).toList.flatten ⊆ l →
    ∃ idx' : Fin (List.length l), l[idx'] = elt := by
      intros H
      apply in_list_idx
      apply H
      rw [List.mem_flatten]
      apply Exists.intro (elt :: v[↑idx])
      simpa [Vector.mem_set]

  theorem vec_set_in (v : Vector (List α) n) (idx : Fin n) (elt : α) :
    elt ∈ (Vector.set v idx (elt :: v[idx]))[idx] := by simpa

  theorem vec_set_in_flatten (v : Vector (List α) n) (idx : Fin n) (elt : α) :
    elt ∈ (Vector.set v idx (elt :: v[↑idx])).toList.flatten := by
      simp only [Fin.getElem_fin, List.mem_flatten, Vector.mem_toList_iff]
      exists (elt :: v[↑idx])
      and_intros <;> simpa [Vector.mem_set]

  theorem vec_set_subset {v : Vector (List α) n} {idx : Fin n} {l : List α} {elt : α} :
    (v.set idx (elt :: v[idx])).toList.flatten ⊆ l →
    ∃ idx' : Fin (List.length l), l[idx'] = elt := by
      intros H
      specialize H (vec_set_in_flatten v idx elt)
      rw [List.mem_iff_get] at H
      obtain ⟨n, Hn⟩ := H
      exists n

  theorem vec_set_subset' {v : Vector (List α) n} {idx : Fin n} {l : List α} {elt : α} :
    (v.set idx (elt :: v[idx]))[idx] ⊆ l →
    ∃ idx' : Fin (List.length l), l[idx'] = elt := by
      intros H
      specialize H (vec_set_in v idx elt)
      rw [List.mem_iff_get] at H
      obtain ⟨n, Hn⟩ := H
      exists n

  theorem vec_set_cons_perm {v : Vector (List α) n} {idx1 idx2 : Fin n} {elt : α} :
    (Vector.set v idx1 (elt :: v[idx1])).toList.flatten.Perm
    (Vector.set v idx2 (v[idx2] ++ [elt])).toList.flatten := by sorry

  theorem vec_set_cons_in {v : Vector (List α) n} {idx1 idx2 : Fin n} {elt : α} :
    (Vector.set v idx1 (v[idx1] ++ [elt])).toList.flatten ⊆
    (Vector.set v idx2 (elt :: v[idx2])).toList.flatten := by
      intros x Hx
      simp only [Fin.getElem_fin, List.mem_flatten, Vector.mem_toList_iff] at ⊢ Hx
      obtain ⟨l, Hl1, Hl2⟩ := Hx
      sorry

  theorem vec_set_cons_remove_in {v : Vector (List α) n} {idx1 : Fin n} {l} {idx2 : Fin (List.length l)} {elt : α} :
    l[idx2] = elt →
    (v.set idx1 (elt :: v[idx1])).toList.flatten ⊆ l →
    v.toList.flatten ⊆ (l.remove idx2) := by
      intros H1 H2 x Hx
      sorry

   theorem vec_set_reconstruct {v v' : Vector α n} {idx : Fin n} {f : α → α} :
      (∀ idx' : Fin n, ¬(idx' = idx) → v'[idx'] = v[idx']) →
      v'[idx] = f v[idx] →
      v' = v.set idx (f v[idx])
      := by
        intros H1 H2
        -- have Htmp : v' = v'.set idx (f v[idx]) := by
        --   sorry
        -- sorry
        sorry

end DataflowRewriter.Noc
