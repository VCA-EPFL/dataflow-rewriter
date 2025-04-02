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
    intro ident; unfold queue bag; simp
    by_cases ({ inst := InstIdent.top, name := 0 }: InternalPort Nat) = ident
    <;> simpa [OfNat.ofNat, PortMap.getIO_cons]
  output_types := by
    intro ident; unfold queue bag; simp
    by_cases H: ({ inst := InstIdent.top, name := 0 }: InternalPort Nat) = ident
    <;> simpa [*, drunfold, OfNat.ofNat, instOfNatInternalPortNat, instOfNatNat, PortMap.getIO_cons]
  inputs_present := by intros; rfl
  outputs_present := by
    intros ident;
    unfold queue bag
    by_cases ({ inst := InstIdent.top, name := 0 }: InternalPort Nat) = ident
    <;> simpa [*, OfNat.ofNat, instOfNatInternalPortNat, instOfNatNat]

def φ (I S : List T₁) : Prop := I = S

lemma queue_refine_ϕ_bag: queue T₁ ⊑_{φ} bag T₁ := by
  intro i s H; constructor
  · intros ident mid_i v Hrule; exists mid_i, mid_i; and_intros
    · by_cases Hcontains : ((queue T₁).inputs.contains ident)
      · unfold queue at *; dsimp at *; simp at Hcontains
        subst ident;
        rw [PortMap.rw_rule_execution] at Hrule; dsimp at Hrule
        subst mid_i;
        have_hole Hhole: ((bag T₁).inputs.getIO { inst := InstIdent.top, name := 0 }) = _ := by
          unfold bag; unfold OfNat.ofNat instOfNatInternalPortNat instOfNatNat;
          simp [drunfold]; rfl
        rw [PortMap.rw_rule_execution Hhole]; dsimp; subst i; rfl
      · exfalso; exact (PortMap.getIO_not_contained_false Hcontains Hrule)
    · constructor
    · rfl
  · intros ident mid_i v Hrule
    exists mid_i
    and_intros
    · by_cases Hcontains : ((queue T₁).outputs.contains ident)
      · unfold queue at *; dsimp at *; simp at Hcontains
        subst ident
        rw [PortMap.rw_rule_execution] at Hrule; dsimp at *
        unfold bag; dsimp
        simp [*, OfNat.ofNat, instOfNatInternalPortNat, instOfNatNat, PortMap.getIO_cons];
        rw [PortMap.rw_rule_execution (h := by apply PortMap.getIO_cons)]
        dsimp
        subst i; subst s
        exists (Fin.mk 0 (by simpa))
      · exfalso; exact (PortMap.getIO_not_contained_false Hcontains Hrule)
    · rfl
  · intros _ mid_i _ _; exists mid_i

lemma ϕ_indistinguishable:
  ∀ x y, φ x y → Module.indistinguishable (queue T₁) (bag T₁) x y := by
    intros x y Hϕ
    constructor <;> intros ident new_i v H <;> exists new_i
    · unfold queue at *; dsimp at v; dsimp at H
      by_cases Hident: ({ inst := InstIdent.top, name := 0 }: InternalPort Nat) = ident
      · rw [PortMap.rw_rule_execution] at H; dsimp at H
        have_hole Hhole: ((bag T₁).inputs.getIO { inst := InstIdent.top, name := 0 }) = _ := by
          unfold bag; unfold OfNat.ofNat instOfNatInternalPortNat instOfNatNat;
          simp [drunfold]; rfl
        subst ident
        rw [PortMap.rw_rule_execution Hhole]; dsimp; dsimp at H; rw [Hϕ] at H; exact H
      · unfold queue at *
        exfalso
        apply (PortMap.getIO_cons_nil_false _ _ ident)
        · exact Hident
        · exact H
    · unfold queue at *; dsimp at v; dsimp at H
      by_cases Hident: ({ inst := InstIdent.top, name := 0 }: InternalPort Nat) = ident
      · rw [PortMap.rw_rule_execution] at H; dsimp at H
        subst ident
        rw [PortMap.rw_rule_execution (h := by apply PortMap.getIO_cons)]; dsimp; dsimp at H; rw [Hϕ] at H;
        rw [← H]
        exists (Fin.mk 0 (by simpa))
      · unfold queue at *
        exfalso
        apply (PortMap.getIO_cons_nil_false _ _ ident)
        · exact Hident
        · exact H

theorem queue_refine_bag: queue T₁ ⊑ bag T₁ := by
  apply (Module.refines_φ_refines ϕ_indistinguishable queue_refine_ϕ_bag)

end DataflowRewriter.BagQueue
