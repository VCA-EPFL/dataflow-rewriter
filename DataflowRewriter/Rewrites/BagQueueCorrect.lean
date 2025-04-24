/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gurvan Debaussart
-/

import Lean
import Init.Data.BitVec.Lemmas
import Qq

import DataflowRewriter.Simp
import DataflowRewriter.AssocList.Lemmas
import DataflowRewriter.Module
import DataflowRewriter.ExprLow
import DataflowRewriter.Component
import DataflowRewriter.KernelRefl
import DataflowRewriter.Reduce
import DataflowRewriter.List
import DataflowRewriter.ExprHighLemmas
import DataflowRewriter.Tactic
import Mathlib.Tactic

namespace DataflowRewriter.BagQueue

open NatModule

variable {T₁ : Type}

instance : MatchInterface (queue T₁) (bag T₁) where
  input_types := by
    intro ident; unfold queue bag; simp [drnat]
  output_types := by
    intro ident; unfold queue bag; simp
    by_cases H: ({ inst := InstIdent.top, name := 0 }: InternalPort Nat) = ident
    <;> simpa [*, drunfold, drnat, PortMap.getIO_cons]
  inputs_present := by intros; rfl
  outputs_present := by
    intros ident;
    unfold queue bag
    by_cases ({ inst := InstIdent.top, name := 0 }: InternalPort Nat) = ident
    <;> simpa [*, drunfold, drnat]

def φ (I S : List T₁) : Prop := I = S

theorem φ_initial : Module.refines_initial (queue T₁) (bag T₁) φ := by
  intros i _; exists i

theorem queue_refine_ϕ_bag: queue T₁ ⊑_{φ} bag T₁ := by
  prove_refines_φ (queue T₁)
  · exists mid_i, mid_i; subst mid_i; unfold bag
    and_intros
    · rw [PortMap.rw_rule_execution]; subst i; rfl
    · constructor
    · rfl
  · exists mid_i
    and_intros
    · unfold bag; rw [PortMap.rw_rule_execution (h := by apply PortMap.getIO_cons)]
      subst i s; exists (Fin.mk 0 (by simpa))
    · rfl
  · intros _ mid_i _ _; exists mid_i

theorem ϕ_indistinguishable:
  ∀ x y, φ x y → Module.indistinguishable (queue T₁) (bag T₁) x y := by
    intros x y Hϕ
    constructor <;> intros ident new_i v H <;> exists new_i <;> unfold queue at *
    · by_cases Hident: ({ inst := InstIdent.top, name := 0 }: InternalPort Nat) = ident
      · rw [PortMap.rw_rule_execution] at H
        unfold bag; subst ident
        rw [PortMap.rw_rule_execution]; rw [Hϕ] at H; exact H
      · exfalso
        apply (PortMap.getIO_cons_nil_false _ _ ident)
        · exact Hident
        · exact H
    · by_cases Hident: ({ inst := InstIdent.top, name := 0 }: InternalPort Nat) = ident
      · rw [PortMap.rw_rule_execution] at H
        subst ident
        rw [PortMap.rw_rule_execution (h := by apply PortMap.getIO_cons)]; rw [Hϕ] at H;
        rw [←H]
        exists (Fin.mk 0 (by simpa))
      · exfalso
        apply (PortMap.getIO_cons_nil_false _ _ ident)
        · exact Hident
        · exact H

theorem queue_refine_bag: queue T₁ ⊑ bag T₁ := by
  apply (Module.refines_φ_refines ϕ_indistinguishable φ_initial queue_refine_ϕ_bag)

end DataflowRewriter.BagQueue
