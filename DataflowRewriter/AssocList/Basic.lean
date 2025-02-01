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

@[specialize, simp] def eraseAllP {α β} (p : α → β → Bool) : AssocList α β → AssocList α β
  | nil         => nil
  | cons k v es => bif p k v then eraseAllP p es else cons k v (eraseAllP p es)

/-- `O(n)`. Remove the first entry in the list with key equal to `a`. -/
@[inline] def eraseAll {α β} [BEq α] (a : α) (l : AssocList α β) : AssocList α β :=
  eraseAllP (fun k _ => k == a) l

def keysList {α β} (map : AssocList α β) : List α :=
  map.toList.map (·.fst)

def valsList {α β} (map : AssocList α β) : List β :=
  map.toList.map (·.snd)

def disjoint_keys {α β γ} [DecidableEq α] (a : AssocList α β) (b : AssocList α γ) : Bool :=
  a.keysList.inter b.keysList = []

def disjoint_vals {α β γ} [DecidableEq γ] (a : AssocList α γ) (b : AssocList β γ) : Bool :=
  a.valsList.inter b.valsList = []

def filter {α β} (f : α → β → Bool) (l : AssocList α β) :=
  l.foldl (λ c a b => if f a b then c.cons a b else c) (∅ : AssocList α β)

def mem {α β} [BEq α] (a : α) (b : β) (l : AssocList α β) : Prop :=
  l.find? a = some b

def inverse {α β} : AssocList α β → AssocList β α
| .nil => .nil
| .cons a b xs => xs.inverse |>.cons b a

def beq_left_ooo {α β} [DecidableEq α] [DecidableEq β] (a b : AssocList α β) : Bool :=
  match a with
  | .cons k v a' =>
    match b.find? k with
    | some v' => v = v' ∧ beq_left_ooo a' b
    | none => false
  | .nil => true

def beq_ooo {α β} [DecidableEq α] [DecidableEq β] (a b : AssocList α β) : Bool :=
  beq_left_ooo a b ∧ beq_left_ooo b a

def filterId {α} [DecidableEq α] (p : AssocList α α) : AssocList α α :=
  p.filter (λ a b => a ≠ b)

def subsetOf {α β} [DecidableEq α] (a b : AssocList α β) : Prop :=
  ∀ i v, a.find? i = .some v → b.find? i = .some v

def EqExt {α β} [DecidableEq α] (a b : AssocList α β) : Prop :=
  -- a.subsetOf b ∧ b.subsetOf a
  ∀ i, a.find? i = b.find? i

theorem EqExt.refl {α β} [DecidableEq α] (a : AssocList α β) : a.EqExt a := by simp [EqExt]
theorem EqExt.symm {α β} [DecidableEq α] {b a : AssocList α β} : a.EqExt b → b.EqExt a := by simp +contextual [EqExt]
theorem EqExt.trans {α β} [DecidableEq α] {a b c : AssocList α β} : a.EqExt b → b.EqExt c → a.EqExt c := by
  simp +contextual [EqExt]

instance AssocListExtSetoid {α β} [DecidableEq α] : Setoid (AssocList α β) :=
  ⟨EqExt, ⟨EqExt.refl, EqExt.symm, EqExt.trans⟩⟩

axiom beq_ooo_ext {α β} [DecidableEq α] [DecidableEq β] (a b : AssocList α β) :
  a.EqExt b ↔ a.beq_ooo b

def DecidableEqExt {α β} [DecidableEq α] [DecidableEq β] (a b : AssocList α β) : Decidable (EqExt a b) :=
  if h : a.beq_ooo b then isTrue ((beq_ooo_ext a b).mpr h)
  else isFalse (fun h' => by apply h; rw [← beq_ooo_ext]; assumption)

instance {α β} [DecidableEq α] [DecidableEq β] : DecidableRel (@EqExt α β _) := DecidableEqExt

def wf {α β} (a : AssocList α β) : Prop := a.keysList.Nodup

def invertible {α} [DecidableEq α] (p : AssocList α α) : Prop :=
  p.filterId.keysList.inter p.inverse.filterId.keysList = ∅ ∧ p.keysList.Nodup ∧ p.inverse.keysList.Nodup

def bijectivePortRenaming {α} [DecidableEq α] (p : AssocList α α) (i: α) : α :=
  let p' := p.inverse
  if p.filterId.keysList.inter p'.filterId.keysList = ∅ && p.keysList.Nodup && p'.keysList.Nodup then
    let map := p.filterId.append p'.filterId
    map.find? i |>.getD i
  else i

/- With the length argument this should be true, and we can easily check length in practice. -/
axiom bijectivePortRenaming_EqExt {α} [DecidableEq α] (p p' : AssocList α α) :
  p.EqExt p' → p.wf → p'.wf → bijectivePortRenaming p = bijectivePortRenaming p'
  -- intro Heq Hwf Hwf'; ext i
  -- simp [bijectivePortRenaming]
  -- sorry

axiom invertibleMap {α} [DecidableEq α] {p : AssocList α α} {a b} :
  invertible p →
  (p.filterId.append p.inverse.filterId).find? a = some b → (p.filterId.append p.inverse.filterId).find? b = some a

end Batteries.AssocList
