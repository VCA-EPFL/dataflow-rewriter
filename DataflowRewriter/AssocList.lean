/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Batteries

namespace Batteries.AssocList

deriving instance DecidableEq for AssocList
deriving instance Repr for AssocList

def append {α β} (a b : AssocList α β) : AssocList α β :=
  match a with
  | .nil => b
  | .cons x y xs =>
    .cons x y <| xs.append b

instance {α β} : Append (AssocList α β) := ⟨ append ⟩

def keysList {α β} (map : AssocList α β) : List α :=
  map.toList.map (·.fst)

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

end Batteries.AssocList
