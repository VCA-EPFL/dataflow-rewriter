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
        · rw [H]; apply Exists.intro ⟨0, by simpa⟩; simpa
        · obtain ⟨i, Hi'⟩ := HR H; exists ⟨i + 1, by simpa⟩

  def fin_range (sz : Nat) : List (Fin sz) :=
    List.replicate sz 0
    |>.mapFinIdx (λ i _ h => ⟨i, by rwa [List.length_replicate] at h⟩)

  def lift_fin {sz : Nat} (n : Fin sz) : Fin (sz + 1) :=
    ⟨n.1 + 1, by simp only [Nat.add_lt_add_iff_right, Fin.is_lt] ⟩

  def fin_range' (sz : Nat) : List (Fin sz) :=
    match sz with
    | 0 => []
    | sz' + 1 => ⟨0, Nat.zero_lt_succ _⟩ :: (fin_range' sz').map lift_fin

  theorem map_mapFinIdx {α β δ} (l : List α) (f : (i : Nat) → α → (h : i < l.length) → β) (g : β → δ) :
    (l.mapFinIdx f).map g = l.mapFinIdx (λ i v h => g (f i v h)) := by
      revert f g
      induction l with
      | nil => intros _ _; rfl
      | cons hd tl HR =>
        intro f g
        simp only [List.mapFinIdx_cons, List.map_cons, HR, List.length_cons]

  theorem fin_range_eq {sz : Nat} :
    fin_range sz = fin_range' sz := by
      induction sz with
      | zero => rfl
      | succ n HR =>
        dsimp [fin_range']; rw [←HR]; dsimp [fin_range]
        simp only [
          List.replicate, List.length_cons, List.mapFinIdx_cons, Fin.zero_eta,
          map_mapFinIdx, lift_fin
        ]

  theorem fin_in_fin_range (sz : Nat) (i : Fin sz) : i ∈ fin_range sz := by
    simp only [fin_range, List.mem_mapFinIdx, List.length_replicate]
    exists i.1, i.2

  theorem fin_range_len (sz : Nat) :
    (fin_range sz).length = sz := by
      induction sz with
      | zero => rfl
      | succ sz HR => simpa [fin_range, HR]

  def fin_conv {sz : Nat} (i : Fin (fin_range sz).length) : Fin sz :=
    Fin.mk i.1 (by cases i; rename_i v h; rw [fin_range_len] at h; simpa)

  theorem mapFinIdx_length {α β} (l : List α) (f : (i : Nat) → α → (h : i < l.length) → β) :
    (List.mapFinIdx l f).length = l.length := by
      simpa only [List.length_mapFinIdx]

  theorem mapFinIdx_get {α β} (l : List α) (f : (i : Nat) → α → (h : i < l.length) → β) (i : Fin (List.mapFinIdx l f).length) :
    (List.mapFinIdx l f).get i = f i l[i] (by rw [←mapFinIdx_length l f]; exact i.2) := by
      simpa

  theorem fin_range_get {sz : Nat} {i : Fin (fin_range sz).length} :
    (fin_range sz).get i = fin_conv i := by
    dsimp [fin_range]
    apply mapFinIdx_get

  theorem fin_cast {sz sz' : Nat} (h : sz = sz' := by rfl) :
    Fin sz = Fin sz' := by subst h; rfl

  -- RelIO ---------------------------------------------------------------------

  @[simp] abbrev RelIO (S : Type) := Σ T : Type, S → T → S → Prop

  def RelIO.liftFinf {α : Type _} (n : Nat) (f : Fin n → α) : PortMap Nat α :=
    fin_range n |>.map (λ i => ⟨↑i.toNat, f i⟩) |>.toAssocList

  theorem RelIO.liftFinf_in {S} {ident : InternalPort Nat} {n : Nat} {f : Fin n → RelIO S}:
    AssocList.contains ident (RelIO.liftFinf n f) = true
    → ∃ i : Fin n, ident = i := by
        -- dsimp [liftFinf, fin_range]
        -- simp only [
        --   AssocList.contains_eq, List.toList_toAssocList, List.any_map,
        --   List.any_eq_true, List.mem_mapFinIdx, List.length_replicate,
        --   Function.comp_apply, beq_iff_eq, forall_exists_index, and_imp
        -- ]
        -- intros x1 x2 H1 H2 H3
        -- subst ident
        -- exists x1
        sorry

  theorem RelIO.liftFinf_get {S} {n : Nat} {i : Fin n} {f : Fin n → RelIO S}:
    (RelIO.liftFinf n f).getIO i = f i := by sorry

  theorem RelIO.mapVal {α β} {n : Nat} {f : Fin n → α} {g : α → β} :
    AssocList.mapVal (λ _ => g) (RelIO.liftFinf n f) = RelIO.liftFinf n (λ i => g (f i)) := by
      -- dsimp [RelIO.liftFinf, fin_range]
      -- rw [AssocList.mapVal_map_toAssocList]
      sorry

  -- RelInt --------------------------------------------------------------------

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
      sorry
      -- and_intros
      -- · exists i; and_intros
      --   · apply fin_in_fin_range
      --   · rfl
      -- · simpa

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

  -- Random --------------------------------------------------------------------

  theorem list_foldl_foldl_map {α β γ} {l : List (List α)} {h : List α → List β}
  {g : γ → γ} {f : γ → β → γ} {acc : γ} :
    List.foldl (λ acc i => List.foldl f (g acc) (h i)) acc l
    = List.foldl (λ acc i => List.foldl f (g acc) i) acc (List.map h l) := by
      induction l generalizing acc with
      | nil => rfl
      | cons hd tl HR => simpa [HR]

  -- theorem list_foldl_foldl_map {α β γ} {l : List (List α)} {h : List α → List β}
  -- {g : γ → γ} {f : γ → β → γ} {acc : γ} :
  --   List.foldl (λ acc i => List.foldl f (g acc) i) acc (List.map h l)
  --   = ???
  --    := by sorry

  -- Problem: We need to get rid of the inside `g acc`, meaning we need to have
  -- it below...
  -- We can do it by folding with a new function which applies `g` to the acc ?

  theorem list_foldl_foldl_flatten {α β} {l : List (List α)} {f} {acc : β} :
  List.foldl (λ acc i => List.foldl f acc i) acc l = List.foldl f acc l.flatten
  := by
    induction l generalizing acc with
    | nil => rfl
    | cons hd tl HR => simpa [HR]

  -- PLists --------------------------------------------------------------------

  def PListL''.{u} {β : Type _} (l : List β) (acc : Type u) (α : Type u) :=
    List.foldl (λ acc i => α × acc) acc l

  def PListL' (acc : Type _) (α : Type _) (n : Nat) :=
    PListL'' (List.replicate n 0) acc α

  theorem PListL''_toPListL' {β} {l : List β} {acc : Type _} :
    PListL'' l acc α = PListL' acc α (List.length l) := by
      induction l generalizing acc with
      | nil => rfl
      | cons hd tl HR => simp [PListL', PListL'', List.replicate] at HR ⊢; rw [HR]

  def PListL := PListL' Unit

  theorem PListL_succ' (acc : Type _) (α : Type _) (n : Nat) :
    PListL' acc α (n + 1) = (α × (PListL' acc α n)) := by
    induction n generalizing acc with
    | zero => rfl
    | succ n HR => simp [PListL', PListL'', List.replicate] at HR ⊢; rw [HR]

  theorem PListL_zero {α : Type _} :
    PListL α 0 = Unit := by rfl

  theorem PListL_succ {α : Type _} {n : Nat} :
    PListL α (n + 1) = (α × (PListL α n)) := by apply PListL_succ'

  def PListL.replicate {α : Type _} (n : Nat) (v : α) : PListL α n :=
    match n with
    | 0 => PListL_zero.mpr ()
    | n + 1 => PListL_succ.mpr (v, PListL.replicate n v)

  def PListL.toList {α n} (pl : PListL α n) : List α :=
    match n with
    | 0 => []
    | n + 1 =>
      have pl' := PListL_succ.mp pl
      pl'.1 :: PListL.toList pl'.2

  def PListL.ofList {α n} (l : List α) (h : List.length l = n) : PListL α n :=
    match n with
    | 0 => PListL_zero.mpr ()
    | n + 1 =>
      match l with
      | [] => by simp only [List.length_nil, Nat.right_eq_add, Nat.add_eq_zero, Nat.succ_ne_self, and_false] at h
      | hd :: tl =>
        PListL_succ.mpr (hd, PListL.ofList tl (by simp only [List.length_cons, Nat.add_right_cancel_iff] at h; exact h))

  def PListL.ofVector {α n} (v : Vector α n) : PListL α n :=
    PListL.ofList v.toList sorry

  def PListL.get' {α n} (pl : PListL α n) (i : Nat) (hLt : i < n) : α :=
    match n with
    | 0 => by contradiction
    | n' + 1 =>
      have pl' := PListL_succ.mp pl
      match i with
      | 0 => pl'.1
      | i' + 1 =>
        PListL.get' pl'.2 i' (by simp only [Nat.add_lt_add_iff_right] at hLt; exact hLt)

  def PListL.get {α n} (pl : PListL α n) (i : Fin n) : α :=
    PListL.get' pl i.1 i.2

  -- DPList --------------------------------------------------------------------

  abbrev DPList'.{u} {α : Type _} (acc : Type u) (l : List α) (f : α → Type u) :=
    List.foldr (λ i acc => f i × acc) acc l

  abbrev DPList {α : Type _} := @DPList' α Unit

  theorem DPList_zero {α} {f : α → Type _} :
    DPList [] f = Unit := by rfl

  theorem DPList_succ' {α : Type _} {hd : α} {tl : List α} {acc : Type _} {f : α → Type _} :
    DPList' acc (hd :: tl) f = (f hd × (DPList' acc tl f)) := by
      rfl

  theorem DPList_succ {α : Type _} {hd : α} {tl : List α} {f : α → Type _} :
    DPList (hd :: tl) f = (f hd × (DPList tl f)) := by
      rfl

  def DPList.get' {α} {l : List α} {f} (pl : DPList l f) (i : Nat) (h : i < List.length l) : f (l.get (Fin.mk i h)) :=
    match l with
    | [] => by contradiction
    | hd :: tl =>
      have pl' := DPList_succ.mp pl
      match i with
      | 0 => pl'.1
      | i' + 1 => pl'.2.get' i' (by simp only [List.length_cons, Nat.add_lt_add_iff_right] at h; exact h)

  def DPList.get {α} {l : List α} {f} (pl : DPList l f) (i : Fin (List.length l)) : f (l.get i) :=
    DPList.get' pl i.1 i.2

  ------------------------------------------------------------------------------

  abbrev DPVector'.{u} {α n} (acc : Type u) (l : Vector α n) (f : α → Type u) :=
    Vector.foldr (λ i acc => f i × acc) acc l

  abbrev DPVector {α n} := @DPVector' α n Unit

  theorem DPVector_succ {α n} {v : Vector α (n + 1)} {f : α → Type _} :
    DPVector v f = (f v[0] × (DPVector v.tail f)) := by
      simp [DPVector, DPVector', Vector.foldr]
      sorry

  def DPVector.get {α n} {v : Vector α n} {f} (pv : DPVector v f) (i : Fin n) : f (v.get i) :=
    let ⟨idx, Hidx⟩ := i
    match n with
    | 0 => by contradiction
    | n' + 1 =>
      have pv' := DPVector_succ.mp pv
      match idx with
      | 0 => pv'.1
      | idx' + 1 =>
        -- We need ANOTHER cast here…
        -- DPVector.get pv'.2 ⟨idx', by simp at Hidx; simpa⟩
        sorry

end DataflowRewriter.Noc
