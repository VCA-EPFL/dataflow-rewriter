/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hamza Remmal
-/

import DataflowRewriter.Module
import DataflowRewriter.Examples.Flushability.ConfluentModule
import DataflowRewriter.Examples.Flushability.DeterministicModule
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

def pf (mod: Module Ident S) (s: S) :=
  ∀ r ∈ mod.internals, ∀ s', ¬ r s s'

omit [DecidableEq Ident] in
theorem pf_is_terminal {mod: Module Ident S} :
  ∀ s₁ s₂, pf mod s₁ → existSR mod.internals s₁ s₂ → s₁ = s₂ :=
by
  intro s₁ s₂ h₁ h₂
  cases h₂ with
  | done => rfl
  | step _ mid _ rule h₃ =>
    specialize h₁ rule h₃ mid
    contradiction

class Flushable (mod: Module Ident S) where
 can_flush: ∀ s, ∃ s', existSR mod.internals s s' ∧ pf mod s'

inductive flushesTo: (Module Ident S) → S → S → Prop where
| mk: ∀ mod s₁ s₂,
  existSR mod.internals s₁ s₂
  → pf mod s₂
  → flushesTo mod s₁ s₂

def rflushed (mod: Module Ident S) (rule: RelIO S): RelIO S :=
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


section

  variable {Ident S : Type _}
  variable [DecidableEq Ident]

class OutputPreservesFlushability (mod: Module Ident S) where
  rule: ∀ ident s₁ v s₂,
    pf mod s₁
  → (mod.outputs.getIO ident).snd s₁ v s₂
  →  pf mod s₂

end
section

variable {Ident S: Type _}
variable [DecidableEq Ident]
variable {mod: Module Ident S}
variable [qc: QuasiConfluent mod]

-- TODO: Does confluence implies uniqueness of the pf state?
-- What I should prove is that if a system is confluent, and it is flushable from the root
-- then the flushing of the common root is also flushable to the same flushed state
-- TODO: Can I weaken the requirements to only need LocalConfluence?
theorem newrule:
  ∀ s₁ s₂ s₃, existSR mod.internals s₁ s₂ → flushesTo mod s₁ s₃ → flushesTo mod s₂ s₃ :=
by
  intro _ _ s₃ h₁ h₂
  obtain ⟨_, _⟩ := h₂
  constructor
  . induction h₁ with
    | done => assumption
    | step _ mid _ _ _ _ _ ih =>
      apply ih
      have: ∃ s₄, existSR mod.internals mid s₄ ∧ existSR mod.internals s₃ s₄ := by
        apply qc.internals <;> assumption
      obtain ⟨s₄, _, _⟩ := this
      have: s₃ = s₄ := by
        apply pf_is_terminal <;> assumption
      subst this
      assumption
  . assumption

end

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

end

section

variable {mod: Module Ident S}

theorem flushed_preserves_input_over_getIO:
  ∀ {ident}, ((flushed mod).inputs.getIO ident).fst = (mod.inputs.getIO ident).fst :=
by
  intro ident
  unfold PortMap.getIO
  iterate 2 rw [<- Option.getD_map Sigma.fst]
  iterate 2 rw [Batteries.AssocList.find?_map_comm]
  rw [preserves_input_types]

theorem flushed_preserves_input_over_getIO':
  ∀ {ident}, (mod.inputs.getIO ident).fst = ((flushed mod).inputs.getIO ident).fst :=
by
  intro; symm; apply flushed_preserves_input_over_getIO

end

section
  variable (mod: Module Ident S)

-- TODO: Find a better name
theorem flushed_inputs_are_rflushed: ∀ ident,
  mod.inputs.contains ident
  → (flushed mod).inputs.getIO ident = rflushed mod (mod.inputs.getIO ident) :=
by
  intros _ h
  dsimp [flushed, rflushed, PortMap.getIO]
  rw [Batteries.AssocList.find?_mapVal]
  rw [<- Batteries.AssocList.contains_find?_iff] at h
  obtain ⟨_, h⟩ := h; rw [h]
  dsimp only [Option.map_some, Option.getD_some]

-- TODO: LocalConfluence should be enough here if newrule holds with local confluence
theorem flushed_reachable_from_nonflushed [lc: QuasiConfluent mod] : ∀ ident s₁ v s₂ s₃,
  ((flushed mod).inputs.getIO ident).snd s₁ v s₃
  → (mod.inputs.getIO ident).snd s₁ (flushed_preserves_input_over_getIO.mp v) s₂
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
  have: ∃ s₄, existSR mod.internals s₂ s₄ ∧ existSR mod.internals w s₄ := by
    apply lc.inputs <;> assumption
  obtain ⟨s₄, _, _⟩ := this
  have: existSR mod.internals s₄ s₃ := by
    have: flushesTo mod w s₃ := by
      constructor <;> assumption
    have: flushesTo mod s₄ s₃ := by
      apply newrule <;> assumption
    obtain ⟨_, _⟩ := this
    assumption
  apply existSR_transitive <;> assumption

theorem flushed_modules_has_flushed_states: ∀ ident s₁ v s₂,
  ((flushed mod).inputs.getIO ident).snd s₁ v s₂ → pf mod s₂ :=
by
  intro ident _ _ _ h
  have HContains: (flushed mod).inputs.contains ident := by
    apply PortMap.rule_contains <;> assumption
  simp only [flushed_preserves_ports] at HContains
  have: ∃ mrule, mod.inputs.find? ident = some mrule := by
    rw [Batteries.AssocList.contains_find?_iff] <;> assumption
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
    (mod.inputs.getIO ident).snd s (flushed_preserves_input_over_getIO.mp v) s''
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

section

variable {Ident S: Type _}
variable [DecidableEq Ident]
variable (mod: Module Ident S)

theorem m_imp_fm [f: Flushable mod] : ∀ ident s₁ v s₂,
  (mod.inputs.getIO ident).snd s₁ v s₂
  → ∃ s₃, ((flushed mod).inputs.getIO ident).snd s₁ (flushed_preserves_input_over_getIO'.mp v) s₃ :=
by
  intros ident _ _ s₂ _
  obtain ⟨s₃, _⟩ := f.can_flush s₂
  use s₃
  have: (flushed mod).inputs.getIO ident = rflushed mod (mod.inputs.getIO ident) := by
    apply flushed_inputs_are_rflushed <;> apply PortMap.rule_contains <;> assumption
  rw [sigma_rw this]
  simp [rflushed]
  use s₂

theorem fm_imp_m: ∀ ident s₁ v s₂,
  ((flushed mod).inputs.getIO ident).snd s₁ v s₂
  → ∃ s₃, (mod.inputs.getIO ident).snd s₁ (flushed_preserves_input_over_getIO.mp v) s₃ :=
by
  intros ident _ _ _ h
  have: (flushed mod).inputs.getIO ident = rflushed mod (mod.inputs.getIO ident) := by
    apply flushed_inputs_are_rflushed
    rw [← flushed_preserves_ports _ _]
    apply PortMap.rule_contains at h
    exact h
  rw [sigma_rw this] at h
  simp [rflushed] at h
  obtain ⟨s₃, _, _⟩ := h
  simp
  use s₃

end
namespace Refinement

variable (mod: Module Ident S)

class RuleMaySwap: Prop where
  inputs: ∀ ident s₁ v s₂ s₃,
    (mod.inputs.getIO ident).snd s₁ v s₂
    → existSR mod.internals s₁ s₃
    → ∃ s₄, (mod.inputs.getIO ident).snd s₃ v s₄ ∧ existSR mod.internals s₂ s₄
  outputs: ∀ ident s₁ v s₂ s₃,
    (mod.outputs.getIO ident).snd s₁ v s₂
    → existSR mod.internals s₁ s₃
    → ∃ s₄, (mod.outputs.getIO ident).snd s₃ v s₄ ∧ existSR mod.internals s₂ s₄

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

section
variable [qc: QuasiConfluent mod] -- TODO: Can we only use local confluence?
variable [sm: RuleMaySwap mod] -- TODO: Can we derive this property from some sort of confluence?
variable [Flushable mod]
variable [opfm: OutputPreservesFlushability mod] -- TODO: Definition of flushed should guarantee this

theorem refinesₐ: mod ⊑_{flushesTo mod} flushed mod :=
by
  unfold Module.refines_φ
  intro init_i init_s h
  apply Module.comp_refines.mk
  . intros ident mid_i v _
    have: ∃ s₄, (mod.inputs.getIO ident).snd init_s v s₄ ∧ existSR mod.internals mid_i s₄ := by
      obtain ⟨_, _⟩ := h
      apply sm.inputs <;> assumption
    obtain ⟨s₄, h₂, _⟩ := this
    obtain h₃ := m_imp_fm mod ident init_s v s₄ h₂
    obtain ⟨s₃, h₃⟩ := h₃
    use s₃, s₃
    and_intros
    . assumption
    . apply existSR_reflexive
    . have: (flushed mod).inputs.getIO ident = rflushed mod (mod.inputs.getIO ident) := by
        apply flushed_inputs_are_rflushed <;> apply PortMap.rule_contains <;> assumption
      rw [sigma_rw this] at h₃
      simp [rflushed] at h₃ <;> clear this
      obtain ⟨s₅, _, _, _⟩ := h₃
      constructor
      . apply existSR_transitive _ _ s₄ _
        . assumption
        . have: ∃ s₆, existSR mod.internals s₄ s₆ ∧ existSR mod.internals s₅ s₆ := by
            apply qc.inputs <;> assumption
          obtain ⟨s₆, _, _⟩ := this
          apply existSR_transitive _ _ s₆ _
          . assumption
          . have: flushesTo mod s₅ s₃ := by
              constructor <;> assumption
            have: flushesTo mod s₆ s₃ := by
              apply newrule <;> assumption
            obtain ⟨_, _⟩ := this
            assumption
      . assumption
  . intros ident mid_i v _
    use init_s
    obtain ⟨_, _⟩ := h
    simp only [exists_and_left]
    and_intros
    . apply existSR_reflexive
    . have: ∃ s₄, (mod.outputs.getIO ident).snd init_s v s₄ ∧ existSR mod.internals mid_i s₄ := by
        apply sm.outputs <;> assumption
      obtain ⟨s₄, _, _⟩ := this
      use s₄
      dsimp [flushed]
      and_intros
      . assumption
      . constructor
        . assumption
        . apply opfm.rule <;> assumption
  . intros rule mid_i _ _
    use init_s
    and_intros
    . apply existSR_reflexive
    . have: existSR mod.internals init_i mid_i := by
        apply existSR_single_step <;> assumption
      have: ∃ s₄, existSR mod.internals mid_i s₄ ∧ existSR mod.internals init_s s₄ := by
          obtain ⟨_, _⟩ := h
          apply qc.internals <;> assumption
      obtain ⟨s₄, _, _⟩ := this
      have: existSR mod.internals init_i mid_i := by
        apply existSR_single_step <;> assumption
      apply newrule <;> assumption

end

end Refinement

end DataflowRewriter
