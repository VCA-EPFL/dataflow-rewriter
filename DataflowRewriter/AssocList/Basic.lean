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

def disjoint_keys {α β γ} [DecidableEq α] (a : AssocList α β) (b : AssocList α γ) : Bool :=
  a.keysList ∩ b.keysList = ∅

def filter {α β} (f : α → β → Bool) (l : AssocList α β) :=
  l.foldl (λ c a b => if f a b then c.cons a b else c) (∅ : AssocList α β)

def mem {α β} [BEq α] (a : α) (b : β) (l : AssocList α β) : Prop :=
  l.find? a = some b

def inverse {α β} : AssocList α β → AssocList β α
| .nil => .nil
| .cons a b xs => xs.inverse |>.cons b a

end Batteries.AssocList
