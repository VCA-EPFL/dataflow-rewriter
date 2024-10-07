/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Batteries

namespace Batteries.AssocList

def append {α β} (a b : AssocList α β) : AssocList α β :=
  match a with
  | .nil => b
  | .cons x y xs => 
    .cons x y <| xs.append b

def modifyKeys {α β} (map : AssocList α β) (f : α → α) : AssocList α β :=
  map.foldl (λ new_map k v => new_map.cons (f k) v) ∅

def keysList {α β} (map : AssocList α β) : List α :=
  map.toList.map (·.fst)

def filter {α β} (f : α → β → Bool) (l : AssocList α β) :=
  l.foldl (λ c a b => if f a b then c.cons a b else c) (∅ : AssocList α β)

end Batteries.AssocList
