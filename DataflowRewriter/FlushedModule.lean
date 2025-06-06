/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hamza Remmal
-/

import DataflowRewriter.Module
import DataflowRewriter.DeterministicModule
import DataflowRewriter.ModuleLemmas
import Mathlib.Tactic

-- TODO: Move this to a more global file
@[reducible] def cast_first {β : Type _ → Type _} {a b : (Σ α, β α)} (h : a = b) : a.fst = b.fst := by
  subst_vars; rfl

-- TODO: Move this to a more global file
theorem sigma_rw {S T : Type _} {m m' : Σ (y : Type _), S → y → T → Prop} {x : S} {y : T} {v : m.fst}
        (h : m = m' := by reduce; rfl) :
  m.snd x v y ↔ m'.snd x ((cast_first h).mp v) y := by
  constructor <;> (intros; subst h; assumption)

namespace DataflowRewriter

  variable {Ident S : Type _}
  variable [DecidableEq Ident]

abbrev ExtRule (S: Type _) := (Σ T: Type _, S → T → S → Prop)
abbrev IntRule (S: Type _) := S → S → Prop

def pf (mod: Module Ident S) (s: S) :=
  ∀ r ∈ mod.internals, ∀ s', ¬ r s s'

def rflushed (mod: Module Ident S) (rule: ExtRule S): ExtRule S :=
  ⟨rule.1 , λ s ret s'' => ∃ s', rule.2 s ret s' ∧ existSR mod.internals s' s'' ∧ pf mod s''⟩

def iflushed (mod: Module Ident S) :=
  λ s => ∃ s', mod.init_state s ∧ existSR mod.internals s s' ∧ pf mod s'

def flushed (mod: Module Ident S): Module Ident S :=
  {
    inputs     := mod.inputs.mapVal (λ _ v => rflushed mod v), -- transform all the rules to flushed rules
    internals  := [],                                          -- no more internal rules, inputs takes up the role of internals
    outputs    := mod.outputs,                                 -- output rules remains unchanges
    init_state := iflushed mod                                 -- Make sure to flush the initial state
  }

---------------------------------------------------------------------------------------------------
----
---------------------------------------------------------------------------------------------------

section
  variable (mod: Module Ident S)

omit [DecidableEq Ident] in
theorem preserves_input_types:
  (flushed mod).inputs.mapVal (λ _ v => Sigma.fst v) = mod.inputs.mapVal (λ _ v => Sigma.fst v) :=
by
  rw [flushed, Batteries.AssocList.mapVal_mapVal]
  dsimp [rflushed]

omit [DecidableEq Ident] in
theorem flushed_preserves_outputs:
  (flushed mod).outputs = mod.outputs :=
by
  rfl

theorem flushed_preserves_input_over_getIO:
  ∀ ident, ((flushed mod).inputs.getIO ident).fst = (mod.inputs.getIO ident).fst :=
by
  intro ident
  unfold PortMap.getIO
  iterate 2 rw [<- Option.getD_map Sigma.fst]
  iterate 2 rw [Batteries.AssocList.find?_map_comm]
  rw [preserves_input_types]

theorem flushed_preserves_input_over_getIO' {Ident S: Type _} [DecidableEq Ident] (mod: Module Ident S):
  ∀ ident, (mod.inputs.getIO ident).fst = ((flushed mod).inputs.getIO ident).fst :=
by
  intro; symm; apply flushed_preserves_input_over_getIO

theorem flushed_preserves_ports:
  ∀ ident, (flushed mod).inputs.contains ident ↔ mod.inputs.contains ident :=
by
  intro ident
  dsimp [flushed]
  cases mod.inputs with
  | nil => simp [Batteries.AssocList.mapVal]
  | cons k hd tl =>
      dsimp [Batteries.AssocList.mapVal, Batteries.AssocList.contains, Batteries.AssocList.any] at *
      by_cases h: k = ident
      . subst h; simp
      . have: (k == ident) = false := decide_eq_false h
        simp [this]

-- TODO: Find a better name
theorem flushed_inputs_are_rflushed: ∀ ident,
  mod.inputs.contains ident
  → (flushed mod).inputs.getIO ident = rflushed mod (mod.inputs.getIO ident) :=
by
  intros _ h
  dsimp [flushed, rflushed, PortMap.getIO]
  rw [Batteries.AssocList.find?_mapVal]
  apply AssocList.contains_find?_exists at h
  obtain ⟨_, h⟩ := h; rw [h]
  dsimp only [Option.map_some, Option.getD_some]

-- Hamza: Introduce [Deterministic mod]? Is it really needed?
-- Hamza: Yes, if the underlying module is not deterministic, we can't guarantee that
--        the flushed module will behave the same way as the non-flushed version
open Module.Determinism in
theorem flushed_reachable_from_nonflushed [DeterministicInputs mod] : ∀ ident s₁ v s₂ s₃,
  ((flushed mod).inputs.getIO ident).snd s₁ v s₃
  → (mod.inputs.getIO ident).snd s₁ ((flushed_preserves_input_over_getIO mod ident).mp v) s₂
  → existSR mod.internals s₂ s₃ :=
by
  intro ident s₁ v s₂ s₃ h₁ h₂
  have: (flushed mod).inputs.getIO ident = rflushed mod (mod.inputs.getIO ident) := by
    apply flushed_inputs_are_rflushed
    apply PortMap.rule_contains
    assumption
  rw [sigma_rw this] at h₁
  dsimp [rflushed] at h₁
  obtain ⟨w, _, _, _⟩ := h₁
  have: s₂ = w := by
    rename_i det _ _ _
    apply det.input_deterministic <;> assumption
  subst this
  assumption

theorem flushed_modules_has_flushed_states: ∀ ident s₁ v s₂,
  ((flushed mod).inputs.getIO ident).snd s₁ v s₂ → pf mod s₂ :=
by
  intro ident _ _ _ h
  have HContains: (flushed mod).inputs.contains ident := by
    apply PortMap.rule_contains <;> assumption
  simp only [flushed_preserves_ports] at HContains
  have: ∃ mrule, mod.inputs.find? ident = some mrule := by
    apply AssocList.contains_find?_exists <;> assumption
  obtain ⟨_, h₂⟩ := this
  apply PortMap.getIO_some at h₂
  subst h₂
  have: (flushed mod).inputs.getIO ident = rflushed mod (mod.inputs.getIO ident) := by
    apply flushed_inputs_are_rflushed <;> assumption
  clear HContains
  rw [sigma_rw (by assumption)] at h
  dsimp [rflushed] at h
  obtain ⟨_, _, _, _⟩ := h
  assumption

theorem bll: ∀ ident s v s',
  ((flushed mod).inputs.getIO ident).snd s v s'
  → ∃ s'',
    (mod.inputs.getIO ident).snd s ((flushed_preserves_input_over_getIO mod ident).mp v) s''
    ∧ existSR (mod.internals) s'' s' :=
by
  intro ident s v s' h₁
  have: (flushed mod).inputs.getIO ident = rflushed mod (mod.inputs.getIO ident) := by
    have: Batteries.AssocList.contains ident mod.inputs = true := by
      apply PortMap.rule_contains at h₁
      simp only [flushed_preserves_ports] at h₁
      assumption
    apply flushed_inputs_are_rflushed <;> assumption
  rw [sigma_rw this] at h₁
  dsimp [rflushed] at h₁
  obtain ⟨s, _, _, _⟩ := h₁
  use s
  apply And.intro <;> assumption

end


---------------------------------------------------------------------------------------------------
----
---------------------------------------------------------------------------------------------------

namespace Match

instance (mod: Module Ident S): MatchInterface (flushed mod) mod := by
  rw [MatchInterface_simpler_iff]
  rw [preserves_input_types, flushed_preserves_outputs]
  intros <;> and_intros <;> rfl

instance (mod: Module Ident S): MatchInterface mod (flushed mod) := by
  haveI: MatchInterface (flushed mod) mod := by infer_instance
  apply MatchInterface_symmetric <;> assumption

omit S in -- TODO: Looks like this omit is a noop
instance {S₁ S₂: Type _} (mod₁: Module Ident S₁) (mod₂: Module Ident S₂) [MatchInterface mod₁ mod₂]: MatchInterface (flushed mod₁) (flushed mod₂) := by
  have: MatchInterface (flushed mod₁) mod₁ := by infer_instance
  have: MatchInterface mod₂ (flushed mod₂) := by infer_instance
  have: MatchInterface mod₁ (flushed mod₂) := by
    apply MatchInterface_transitive <;> assumption
  apply MatchInterface_transitive <;> assumption

end Match

---------------------------------------------------------------------------------------------------
-----
---------------------------------------------------------------------------------------------------

namespace Refinement

  variable (mod: Module Ident S)

theorem flushed_refines_nonflushed: flushed mod p⊑_{Eq} mod := by
  unfold Module.prefines_φ
  intro init_i init_s Hφ
  subst_vars
  apply Module.pcomp_refines.mk
  -- input rules
  . intro ident mid_i v h
    simp only [eq_mp_eq_cast, exists_and_left, exists_eq_right']
    apply bll at h
    simp at h
    obtain ⟨s', _⟩ := h
    use s'
  -- output rules
  . intro _ mid_i _ _
    use mid_i; simpa
  -- internal rules
  . intro _ mid_i h _
    cases h

end Refinement

end DataflowRewriter
