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

end StateTransition

section TraceInclusion

variable {Ident : Type _}
variable [DecidableEq Ident]
variable {S I : Type _}
variable (imp : Module Ident I)
variable (spec : Module Ident S)
variable [MatchInterface imp spec]

def imp_state_transition : StateTransition (State Ident I) Trace where
  init := fun s => imp.init_state s.state ∧ s.module = imp
  step := step

def spec_state_transition : StateTransition (State Ident S) Trace where
  init := fun s => spec.init_state s.state ∧ s.module = spec
  step := step

def imp_behaviour := @behaviour _ _ (imp_state_transition imp)

def spec_behaviour := @behaviour _ _ (spec_state_transition spec)

def trace_inclusion : Prop :=
  ∀ l, imp_behaviour imp l → spec_behaviour spec l

theorem refines_implies_step_preservation {φ} :
  imp ⊑_{φ} spec →
  ∀ i s i' e,
    φ i s →
    (imp_state_transition imp).step ⟨i, imp⟩ e i' →
    ∃ s_mid s',
      (spec_state_transition spec).step ⟨s, spec⟩ e s_mid
      ∧ (spec_state_transition spec).step s_mid [] s'
      ∧ φ i'.state s'.state := by
  intros href i s i' e hphi hstep
  cases hstep with
  | @input ident i' v v' step =>
    subst v'
    dsimp at *; dsimp at v
    rcases href _ _ hphi with ⟨inp, out, int⟩; clear href out int
    obtain ⟨s1, s2, h1, h2, h3⟩ := inp ident i' v step; clear inp
    exists ⟨s1, spec⟩, ⟨s2, spec⟩
    and_intros
    · constructor
      · apply h1
      · simp; apply MatchInterface.input_types
    · sorry
    · assumption
  | _ => sorry

theorem refines_implies_trace_inclusion :
  imp ⊑ spec →
  trace_inclusion imp spec := by sorry

end TraceInclusion

end Module

end DataflowRewriter
