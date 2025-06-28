/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hamza Remmal
-/

import Graphiti.Module
import Graphiti.ModuleLemmas
import Mathlib.Tactic

namespace Graphiti

  variable {Ident S : Type _}
  variable [DecidableEq Ident]

class DeterministicInputs (mod: Module Ident S) where
  input_deterministic: ∀ ident s₁ v s₂ s₃,
    (mod.inputs.getIO ident).snd s₁ v s₂
    → (mod.inputs.getIO ident).snd s₁ v s₃
    → s₂ = s₃

class DeterministicInternals (mod: Module Ident S) where
  internal_deterministic: ∀ rule ∈ mod.internals , ∀ s₁ s₂ s₃,
    rule s₁ s₂ → rule s₁ s₃ → s₂ = s₃

class DeterministicOutputs (mod: Module Ident S) where
  output_deterministic: ∀ ident s₁ v s₂ s₃,
    (mod.outputs.getIO ident).snd s₁ v s₂
    → (mod.outputs.getIO ident).snd s₁ v s₃
    → s₂ = s₃

class Deterministic (mod: Module Ident S) extends
  DeterministicInputs mod,
  DeterministicInternals mod,
  DeterministicOutputs mod


end Graphiti
