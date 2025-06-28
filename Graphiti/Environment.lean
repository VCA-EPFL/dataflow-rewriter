/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Lean

import DataflowRewriter.Module
import DataflowRewriter.Simp
import DataflowRewriter.ExprHigh
import DataflowRewriter.AssocList.Basic

namespace DataflowRewriter

namespace Env

def subsetOf (ε₁ ε₂ : Env) : Prop :=
  ∀ i v, ε₁.find? i = .some v → ε₂.find? i = .some v

end Env

axiom ε_global : Env

end DataflowRewriter
