/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Lean

import Graphiti.Module
import Graphiti.Simp
import Graphiti.ExprHigh
import Graphiti.AssocList.Basic

namespace Graphiti

namespace Env

def subsetOf (ε₁ ε₂ : Env) : Prop :=
  ∀ i v, ε₁.find? i = .some v → ε₂.find? i = .some v

end Env

axiom ε_global : Env

end Graphiti
