/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.ModuleLemmas
import DataflowRewriter.StateTransition

namespace DataflowRewriter

inductive Trace where
| input : (Σ (T : Type _), T) → Trace
| output : (Σ (T : Type _), T) → Trace

namespace Module

section StateTransition

variable (Ident : Type _)
variable [DecidableEq Ident]
variable (S : Type _)

structure State where
  state : S
  module : Module Ident S

variable {Ident} {S}

inductive step : State Ident S → List Trace → State Ident S → Prop where
| input {st ident s' v v'} :
    (st.module.inputs.getIO ident).snd st.state v s' →
    v' = ⟨(st.module.inputs.getIO ident).fst, v⟩ →
    step st [.input v'] ⟨s', st.module⟩
| output {st ident s' v v'} :
    (st.module.outputs.getIO ident).snd st.state v s' →
    v' = ⟨(st.module.outputs.getIO ident).fst, v⟩ →
    step st [.output v'] ⟨s', st.module⟩
| internal {st r s'} :
  r ∈ st.module.internals →
  r st.state s' →
  step st [] ⟨s', st.module⟩

def state_transition (m : Module Ident S) : StateTransition (State Ident S) Trace where
  init := fun s => m.init_state s.state ∧ s.module = m
  step := step

theorem existSR_implies_empty_steps {m : Module Ident S} {s1 s2} :
  existSR m.internals s1 s2 →
  @star _ _ (state_transition m) ⟨s1, m⟩ [] ⟨s2, m⟩ := by
  intro h
  induction h with
  | done => apply @star.refl _ _ (state_transition m)
  | step init mid final rule hin hrule hexists ih =>
    rw [show [] = [] ++ [] by rfl]
    apply @star.step _ _ (state_transition m)
    rotate_left; apply ih
    constructor <;> assumption

end StateTransition

section TraceInclusion

variable {Ident : Type _}
variable [DecidableEq Ident]
variable {S I : Type _}
variable (imp : Module Ident I)
variable (spec : Module Ident S)

def imp_behaviour := @behaviour _ _ (state_transition imp)

def spec_behaviour := @behaviour _ _ (state_transition spec)

def trace_inclusion : Prop :=
  ∀ l, imp_behaviour imp l → spec_behaviour spec l

section Refinement

variable [mm : MatchInterface imp spec]

theorem refines_implies_step_preservation {φ} :
  imp ⊑_{φ} spec →
  ∀ i s i' e,
    φ i s →
    (state_transition imp).step ⟨i, imp⟩ e i' →
    ∃ s',
      @star _ _ (state_transition spec) ⟨s, spec⟩ e s'
      ∧ φ i'.state s'.state := by
  intros href i s i' e hphi hstep
  cases hstep with
  | @input ident i' v v' step =>
    subst v'
    dsimp at *; dsimp at v
    rcases href _ _ hphi with ⟨inp, out, int⟩; clear href out int
    obtain ⟨s1, s2, h1, h2, h3⟩ := inp ident i' v step; clear inp
    exists ⟨s2, spec⟩
    and_intros
    · rw [show [Trace.input ⟨(imp.inputs.getIO ident).fst, v⟩] = [Trace.input ⟨(imp.inputs.getIO ident).fst, v⟩] ++ [] by rfl]
      apply @star.trans_star _ _ (state_transition spec)
      · apply @star.plus_one _ _ (state_transition spec)
        constructor
        · apply h1
        · simp; apply MatchInterface.input_types
      · apply existSR_implies_empty_steps; assumption
    · assumption
  | @output ident i' v v' step =>
    subst v'
    dsimp at *; dsimp at v
    rcases href _ _ hphi with ⟨inp, out, int⟩; clear href inp int
    obtain ⟨s1, s2, h1, h2, h3⟩ := out ident i' v step; clear out
    exists ⟨s2, spec⟩
    and_intros
    · rw [show [Trace.output ⟨(imp.outputs.getIO ident).fst, v⟩] = [] ++ [Trace.output ⟨(imp.outputs.getIO ident).fst, v⟩] by rfl]
      apply @star.trans_star _ _ (state_transition spec)
      · apply existSR_implies_empty_steps; assumption
      · apply @star.plus_one _ _ (state_transition spec)
        constructor
        · apply h2
        · simp; apply MatchInterface.output_types
    · assumption
  | @internal r i' hin hrule =>
    dsimp at *
    rcases href _ _ hphi with ⟨inp, out, int⟩; clear href inp out
    obtain ⟨s1, h1, h2⟩ := int r i' hin hrule; clear int
    exists ⟨s1, spec⟩
    and_intros
    · apply existSR_implies_empty_steps <;> assumption
    · assumption

theorem refines_implies_star_preservation {φ} :
  imp ⊑_{φ} spec →
  ∀ i s i' e,
    φ i s →
    @star _ _ (state_transition imp) ⟨i, imp⟩ e i' →
    ∃ s',
      @star _ _ (state_transition spec) ⟨s, spec⟩ e s'
      ∧ φ i'.state s'.state := by
  intro href i s i' e hphi hstar
  generalize heq : State.mk i imp = y at *
  induction hstar with
  | refl =>
    cases heq
    exists ⟨s, spec⟩; and_intros
    · apply @star.refl _ _ (state_transition spec)
    · assumption
  | step =>
    cases heq
    sorry

end Refinement

theorem refines_implies_trace_inclusion :
  imp ⊑ spec →
  trace_inclusion imp spec := by
    intros href l b
    obtain ⟨i1, i2, Hi1, Hi2⟩ := b
    have ⟨mm, φ, H1, H2⟩ := href
    unfold refines_initial at H2
    have ⟨Hi1_init, Hi1_mod⟩ := Hi1
    obtain ⟨s1, Hs1_init, Hs1_φ⟩ := H2 i1.state Hi1_init
    exists ⟨s1, spec⟩
    have lred : @star _ _ (state_transition imp) ⟨i1.state, imp⟩ l i2 := by
      have ⟨Hi11, Hi12⟩ := Hi1
      obtain ⟨state, module⟩ := i1
      subst imp
      exact Hi2
    obtain ⟨s2, Hs2_1, Hs2_2⟩ :=
      refines_implies_star_preservation _ _ H1 i1.state s1 i2 l Hs1_φ lred
    exists s2

end TraceInclusion

end Module

end DataflowRewriter
