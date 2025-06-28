/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hamza Remmal
-/

import Graphiti.Module
import Graphiti.ModuleLemmas
import Mathlib.Tactic

namespace Graphiti

variable {Ident S: Type _}
variable [DecidableEq Ident]
variable (mod: Module Ident S)

class DiamondModule: Prop where
  inputs: ∀ ident s₁ v s₂ s₃,
    (mod.inputs.getIO ident).snd s₁ v s₂ → (mod.inputs.getIO ident).snd s₁ v s₃
    → ∃ r₃ ∈ mod.internals, ∃ r₄ ∈ mod.internals, ∃ s₄, r₃ s₂ s₄ ∧ r₄ s₃ s₄
  internals: ∀ s₁ s₂ s₃, ∀ r₁ ∈ mod.internals, ∀ r₂ ∈ mod.internals,
    r₁ s₁ s₂ → r₂ s₁ s₃
    → ∃ r₃ ∈ mod.internals, ∃ r₄ ∈ mod.internals, ∃ s₄, r₃ s₂ s₄ ∧ r₄ s₃ s₄
  outputs: ∀ ident s₁ v s₂ s₃,
    (mod.outputs.getIO ident).snd s₁ v s₂ → (mod.outputs.getIO ident).snd s₁ v s₃
    → ∃ r₃ ∈ mod.internals, ∃ r₄ ∈ mod.internals, ∃ s₄, r₃ s₂ s₄ ∧ r₄ s₃ s₄

class StronglyConfluent: Prop where
  inputs: ∀ ident s₁ v s₂ s₃,
    (mod.inputs.getIO ident).snd s₁ v s₂ → (mod.inputs.getIO ident).snd s₁ v s₃
    → ∃ s₄, (existSR mod.internals s₂ s₄ ∧ ∃ r ∈ mod.internals, r s₃ s₄)
          ∨ (existSR mod.internals s₃ s₄ ∧ ∃ r ∈ mod.internals, r s₂ s₄)
  internals: ∀ s₁ s₂ s₃, ∀ r₁ ∈ mod.internals, ∀ r₂ ∈ mod.internals,
    r₁ s₁ s₂
    → r₂ s₁ s₃
    → ∃ s₄, (existSR mod.internals s₂ s₄ ∧ ∃ r ∈ mod.internals, r s₃ s₄)
          ∨ (existSR mod.internals s₃ s₄ ∧ ∃ r ∈ mod.internals, r s₂ s₄)
  outputs: ∀ ident s₁ v s₂ s₃,
    (mod.outputs.getIO ident).snd s₁ v s₂ → (mod.outputs.getIO ident).snd s₁ v s₃
    → ∃ s₄, (existSR mod.internals s₂ s₄ ∧ ∃ r ∈ mod.internals, r s₃ s₄)
          ∨ (existSR mod.internals s₃ s₄ ∧ ∃ r ∈ mod.internals, r s₂ s₄)

class GloballyConfluent: Prop where
  inputs: ∀ ident s₁ v s₂ s₃,
    (mod.inputs.getIO ident).snd s₁ v s₂ → (mod.inputs.getIO ident).snd s₁ v s₃
    → ∃ s₄, existSR mod.internals s₂ s₄ ∧ existSR mod.internals s₃ s₄
  internals: ∀ s₁ s₂ s₃,
    existSR mod.internals s₁ s₂ → existSR mod.internals s₁ s₃
    → ∃ s₄, existSR mod.internals s₂ s₄ ∧ existSR mod.internals s₃ s₄
  outputs: ∀ ident s₁ v s₂ s₃,
    (mod.outputs.getIO ident).snd s₁ v s₂ → (mod.outputs.getIO ident).snd s₁ v s₃
    → ∃ s₄, existSR mod.internals s₂ s₄ ∧ existSR mod.internals s₃ s₄

class QuasiConfluent: Prop where
  inputs: ∀ ident s₁ v s₂ s₃,
    (mod.inputs.getIO ident).snd s₁ v s₂ → (mod.inputs.getIO ident).snd s₁ v s₃
    → ∃ s₄, existSR mod.internals s₂ s₄ ∧ existSR mod.internals s₃ s₄
  internals: ∀ s₁ s₂ s₃, ∀ r ∈ mod.internals,
    r s₁ s₂ → existSR mod.internals s₁ s₃
    → ∃ s₄, existSR mod.internals s₂ s₄ ∧ existSR mod.internals s₃ s₄
  outputs: ∀ ident s₁ v s₂ s₃,
    (mod.outputs.getIO ident).snd s₁ v s₂ → (mod.outputs.getIO ident).snd s₁ v s₃
    → ∃ s₄, existSR mod.internals s₂ s₄ ∧ existSR mod.internals s₃ s₄

class LocallyConfluent: Prop where
  inputs: ∀ ident s₁ v s₂ s₃,
    (mod.inputs.getIO ident).snd s₁ v s₂ → (mod.inputs.getIO ident).snd s₁ v s₃
    → ∃ s₄, existSR mod.internals s₂ s₄ ∧ existSR mod.internals s₃ s₄
  internals: ∀ s₁ s₂ s₃, ∀ r₁ ∈ mod.internals, ∀ r₂ ∈ mod.internals,
    r₁ s₁ s₂ → r₂ s₁ s₃
    → ∃ s₄, existSR mod.internals s₂ s₄ ∧ existSR mod.internals s₃ s₄
  outputs: ∀ ident s₁ v s₂ s₃,
    (mod.outputs.getIO ident).snd s₁ v s₂ → (mod.outputs.getIO ident).snd s₁ v s₃
    → ∃ s₄, existSR mod.internals s₂ s₄ ∧ existSR mod.internals s₃ s₄

instance diamond_is_strong [dm: DiamondModule mod] : StronglyConfluent mod :=
by
  constructor
  . intros _ _ _ s₂ s₃ _ _
    have: ∃ r₃ ∈ mod.internals, ∃ r₄ ∈ mod.internals, ∃ s₄, r₃ s₂ s₄ ∧ r₄ s₃ s₄ := by
      apply dm.inputs <;> assumption
    obtain ⟨r₃, _, r₄, _, s₄, _, _⟩ := this
    use s₄
    left <;> and_intros
    . apply existSR_single_step _ _ _ r₃ <;> assumption
    . use r₄
  . intros _ s₂ s₃ r₁ _ r₂ _ _ _
    have: ∃ r₃ ∈ mod.internals, ∃ r₄ ∈ mod.internals, ∃ s₄, r₃ s₂ s₄ ∧ r₄ s₃ s₄ := by
      apply dm.internals _ s₂ s₃ r₁ _ r₂ <;> assumption
    obtain ⟨r₃, _, r₄, _, s₄, _, _⟩ := this
    use s₄
    left <;> and_intros
    . apply existSR_single_step _ _ _ r₃ <;> assumption
    . use r₄
  . intros _ _ _ s₂ s₃ _ _
    have: ∃ r₃ ∈ mod.internals, ∃ r₄ ∈ mod.internals, ∃ s₄, r₃ s₂ s₄ ∧ r₄ s₃ s₄ := by
      apply dm.outputs <;> assumption
    obtain ⟨r₃, _, r₄, _, s₄, _, _⟩ := this
    use s₄
    left <;> and_intros
    . apply existSR_single_step _ _ _ r₃ <;> assumption
    . use r₄

instance strong_is_global [sc: StronglyConfluent mod] : GloballyConfluent mod :=
by
  constructor
  . intros _ s₁ _ s₂ s₃ _ _
    have: ∃ s₄, (existSR mod.internals s₂ s₄ ∧ ∃ r ∈ mod.internals, r s₃ s₄) ∨ (existSR mod.internals s₃ s₄ ∧ ∃ r ∈ mod.internals, r s₂ s₄) := by
      apply sc.inputs <;> assumption
    obtain ⟨s₄, h⟩ := this <;> use s₄
    rcases h with h | h <;> obtain ⟨_, _⟩ := h
    . and_intros
      . assumption
      . apply existSR_single_step' <;> assumption
    . and_intros
      . apply existSR_single_step' <;> assumption
      . assumption
  . intro s₁ s₂ s₃ h₁ h₂
    induction h₁ generalizing s₃ with
    | done =>
      use s₃
      simpa [existSR_reflexive]
    | step _ mid final r₁ =>
      induction h₂ generalizing mid with
      | done init =>
        use final
        simp [existSR_reflexive]
        have: existSR mod.internals init mid := by
          apply existSR_single_step <;> assumption
        apply existSR_transitive <;> assumption
      | step i₁ i₂ _ r₂ =>
        have: ∃ s₄, (existSR mod.internals mid s₄ ∧ ∃ r ∈ mod.internals, r i₂ s₄) ∨ (existSR mod.internals i₂ s₄ ∧ ∃ r ∈ mod.internals, r mid s₄) := by
          apply sc.internals _ _ _ r₁ <;> assumption
        obtain ⟨s₄, h⟩ := this
        rcases h with h | h <;> obtain ⟨_, _⟩ := h
        . sorry
        . sorry
  . intros _ s₁ _ s₂ s₃ _ _
    have: ∃ s₄, (existSR mod.internals s₂ s₄ ∧ ∃ r ∈ mod.internals, r s₃ s₄) ∨ (existSR mod.internals s₃ s₄ ∧ ∃ r ∈ mod.internals, r s₂ s₄) := by
      apply sc.outputs <;> assumption
    obtain ⟨s₄, h⟩ := this <;> use s₄
    rcases h with h | h <;> obtain ⟨_, _⟩ := h
    . and_intros
      . assumption
      . apply existSR_single_step' <;> assumption
    . and_intros
      . apply existSR_single_step' <;> assumption
      . assumption

instance global_is_quasi [gc: GloballyConfluent mod] : QuasiConfluent mod :=
by
  constructor
  . exact gc.inputs
  . intros s₁ s₂ s₃ r₁ _ _ h
    cases h with
    | done =>
      use s₂ <;> and_intros
      . apply existSR_reflexive
      . apply existSR_single_step <;> assumption
    | step  _ mid =>
      have: existSR mod.internals s₁ s₃ := by
        have: existSR mod.internals s₁ mid := by
          apply existSR_single_step <;> assumption
        apply existSR_transitive <;> assumption
      have: existSR mod.internals s₁ s₂ := by
        apply existSR_single_step _ _ _ r₁ <;> assumption
      apply gc.internals <;> assumption
  . exact gc.outputs

instance quasi_is_local [qc: QuasiConfluent mod] : LocallyConfluent mod :=
by
  constructor
  . exact qc.inputs
  . intros s₁ _ s₃ r₁ _ _ _ _ _
    have: existSR mod.internals s₁ s₃ := by
      apply existSR_single_step <;> assumption
    apply qc.internals _ _ _ r₁ <;> assumption
  . exact qc.outputs

end Graphiti
