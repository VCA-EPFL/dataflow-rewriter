/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Batteries
import Mathlib

namespace Batteries.AssocList

deriving instance DecidableEq for AssocList
deriving instance Repr for AssocList

def append {α β} (a b : AssocList α β) : AssocList α β :=
  match a with
  | .nil => b
  | .cons x y xs =>
    .cons x y <| xs.append b

instance {α β} : Append (AssocList α β) := ⟨ append ⟩

theorem append_eq {α β} {a b : AssocList α β} :
  (a.append b).toList = a.toList ++ b.toList := by
  induction a generalizing b <;> simp [*, append]

theorem append_eq2 {α β} {a b : AssocList α β} :
  a.append b = (a.toList ++ b.toList).toAssocList := by
  induction a generalizing b <;> simp [*, append]

theorem append_find? {α β} [DecidableEq α] (a b : AssocList α β) (i) :
  (a.append b).find? i = a.find? i
  ∨ (a.append b).find? i = b.find? i := by
  induction a with
  | nil => simp [append]
  | cons k v t ih =>
    by_cases h : k = i
    <;> simp_all [append, List.find?_cons_of_pos, List.find?_cons_of_neg]

def keysList {α β} (map : AssocList α β) : List α :=
  map.toList.map (·.fst)

def disjoint_keys {α β γ} [DecidableEq α] (a : AssocList α β) (b : AssocList α γ) : Bool :=
  a.keysList ∩ b.keysList = ∅

theorem disjoint_cons_left (α β γ) [DecidableEq α] {t : AssocList α β} {b : AssocList α γ} {a y} :
  (cons a y t).disjoint_keys b = true → t.disjoint_keys b = true := by
  unfold disjoint_keys; intros; simp [*]
  simp [Inter.inter, List.instInterOfBEq_batteries, List.inter.eq_1] at *
  rename_i h
  intro el hin; apply h
  simp_all [keysList]

theorem append_find_left {α β} [DecidableEq α] (a b : AssocList α β) {i x} :
  a.find? i = some x →
  (a.append b).find? i = some x := by
  induction a with
  | nil => simp
  | cons a y t ih =>
    intro hfind
    simp only [append]
    rw [Batteries.AssocList.find?.eq_2] at hfind ⊢
    split <;> rename_i _ heq
    · simp_all
    · simp only [heq] at hfind; solve_by_elim

theorem append_find_right {α β} [DecidableEq α] (a b : AssocList α β) {i} :
  a.find? i = none →
  (a.append b).find? i = b.find? i := by
  induction a with
  | nil => simp [append]
  | cons a y t ih =>
    intro hfind
    simp only [append]
    rw [Batteries.AssocList.find?.eq_2] at hfind ⊢
    split <;> rename_i _ heq
    · simp_all
    · simp only [heq] at hfind; solve_by_elim


def filter {α β} (f : α → β → Bool) (l : AssocList α β) :=
  l.foldl (λ c a b => if f a b then c.cons a b else c) (∅ : AssocList α β)

def mem {α β} [BEq α] (a : α) (b : β) (l : AssocList α β) : Prop :=
  l.find? a = some b

def inverse {α β} : AssocList α β → AssocList β α
| .nil => .nil
| .cons a b xs => xs.inverse |>.cons b a

private theorem map_keys_list' {α β γ} [DecidableEq α] {f : α → β → γ} {l : List (α × β)} {ident val} :
  List.find? (fun x => x.fst == ident) l = some val →
  List.find? ((fun x => x.fst == ident) ∘ fun x => (x.fst, f x.fst x.snd)) l = some (ident, val.snd) := by
  induction l generalizing ident val <;> simp_all
  rename_i head tail iH
  intro Hfirst
  rcases Hfirst with ⟨ h1, h2 ⟩ | ⟨ h1, h2 ⟩
  subst_vars; left; simp
  right; and_intros; assumption
  apply iH
  assumption

theorem map_keys_list {α β γ} [DecidableEq α] {ident} {l : AssocList α β} {f : α → β → γ} :
    (l.mapVal f).find? ident = (l.find? ident).map (f ident) := by
  simp [find?_eq]
  cases h : List.find? (fun x => x.fst == ident) l.toList <;> simp_all
  · assumption
  · rename_i val
    refine ⟨ ident, val.snd, ?_ ⟩
    and_intros <;> try rfl
    apply map_keys_list'; assumption

theorem mapKey_toList {α β} {l : AssocList α β} {f : α → α} :
  l.mapKey f = (l.toList.map (λ | (a, b) => (f a, b))).toAssocList := by
  induction l <;> simp [*]

theorem mapKey_toList2 {α β} {l : AssocList α β} {f : α → α} :
  (l.mapKey f).toList = (l.toList.map (λ | (a, b) => (f a, b))) := by
  induction l <;> simp [*]

theorem contains_none {α β} [DecidableEq α] {m : AssocList α β} {ident} :
    ¬ m.contains ident →
    m.find? ident = none := by
  intros H; rw [Batteries.AssocList.contains_eq] at H
  rw [Batteries.AssocList.find?_eq]
  rw [Option.map_eq_none', List.find?_eq_none]; intros x H
  rcases x with ⟨ a, b⟩
  simp at *; unfold Not; intros; apply H
  subst_vars; assumption

theorem contains_some {α β} [DecidableEq α] {m : AssocList α β} {ident} :
    m.contains ident →
    (m.find? ident).isSome := by
  intros H; rw [Batteries.AssocList.contains_eq] at H; simp at H; rcases H with ⟨ a, H ⟩
  simp [*]; constructor; assumption

theorem contains_some2 {α β} [DecidableEq α] {m : AssocList α β} {ident} :
    (m.find? ident).isSome →
    m.contains ident := by
  intro; by_cases contains ident m = true; assumption
  rename_i a b; apply contains_none at b
  rw [b] at a; contradiction

theorem contains_some3 {α β} [DecidableEq α] {m : AssocList α β} {ident x} :
    m.find? ident = some x →
    m.contains ident := by
  intro h; apply contains_some2; rw [h]; rfl

theorem keysList_find {α β} [DecidableEq α] {m : AssocList α β} {ident} :
  (m.find? ident).isSome → ident ∈ m.keysList := by simp_all [keysList]

theorem keysList_find2 {α β} [DecidableEq α] {m : AssocList α β} {ident} :
  ident ∈ m.keysList → (m.find? ident).isSome := by simp_all [keysList]

theorem notkeysList_find2 {α β} [DecidableEq α] {m : AssocList α β} {ident} :
  ident ∉ m.keysList → m.find? ident = none := by
  have : ¬ (m.find? ident).isSome → m.find? ident = none := by
    intro h; simp at h; simp
    skip; intros; unfold Not; intros; apply h; subst_vars; assumption
  intro; apply this; unfold Not; intros; simp_all [keysList]

theorem append_find_right_disjoint {α β} [DecidableEq α] (a b : AssocList α β) {i x} :
  a.disjoint_keys b →
  b.find? i = some x →
  (a.append b).find? i = some x := by
  induction a with
  | nil => simp [append]
  | cons a y t ih =>
    intro hdisj hfind
    simp only [append]
    rw [Batteries.AssocList.find?.eq_2]
    split <;> rename_i _ heq
    · exfalso; clear ih;
      simp_all only [disjoint_keys]
      simp [Inter.inter, List.instInterOfBEq_batteries, List.inter.eq_1] at hdisj
      apply hdisj; constructor; simp at heq; subst_vars
      apply keysList_find; rw [Option.isSome_iff_exists]
      solve_by_elim
    · solve_by_elim [disjoint_cons_left]

end Batteries.AssocList
