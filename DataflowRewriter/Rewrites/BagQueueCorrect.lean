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

-- TODO: Move elsewhere
theorem rw_rule_execution {S : Type _} {a b : Σ (T : Type _), S → T → S → Prop}
{s s'} {v : a.fst} (h : a = b := by simp [drunfold]; rfl) :
  a.snd s v s' ↔ b.snd s ((Module.cast_first h).mp v) s' := by subst_vars; rfl

-- TODO: Move elsewhere
@[simp] lemma cons_find? : ∀ {α} [HDEq : DecidableEq (InternalPort α)] β x v (pm: PortMap α β),
  (Batteries.AssocList.find? x (Batteries.AssocList.cons x v pm)) = v := by
   simpa

-- TODO: Move elsewhere
@[simp] lemma getIO_cons {Ident} [DecidableEq Ident] {S} (pm : PortMap Ident ((T : Type) × (S → T → S → Prop))) x v:
    (PortMap.getIO (Batteries.AssocList.cons x v pm) x) = v := by
    unfold PortMap.getIO; simpa

-- TODO: Move elsewhere
lemma getIO_not_contained_false
  {Ident} [DecidableEq Ident] {S: Type}
  (pm : PortMap Ident ((T : Type) × (S → T → S → Prop))) x1 x2 x3 x4:
    ¬(pm.contains x1) → (pm.getIO x1).snd x2 x3 x4 → False := by
    intros H1 H2
    apply Batteries.AssocList.contains_none at H1
    apply PortMap.getIO_none at H1;
    rw [rw_rule_execution (h := H1)] at H2;
    dsimp at H2

-- TODO: Move elsewhere
lemma getIO_cons_false
  {Ident} [DecidableEq Ident] {S}
  (pm : PortMap Ident ((T : Type) × (S → T → S → Prop))) x1 v x2 x3 x4 x5:
    ¬(x1 = x2) →
    ¬(pm.contains x2) →
    (PortMap.getIO (Batteries.AssocList.cons x1 v pm) x2).snd x3 x4 x5 → False := by
  revert x2 x3 x4 x5
  generalize Hpm' : (Batteries.AssocList.cons x1 v pm) = pm'
  intros x2 x3 x4 x5 H1 H2 H3
  have Hcontains : ¬ pm'.contains x2 := by
    rw [← Hpm']; simp; split_ands
    · exact H1
    · simp at H2; exact H2
  stop
  exact (getIO_not_contained_false pm' x2 x3 x4 x5 Hcontains H3)

lemma getIO_cons_nil_false
  {Ident} [DecidableEq Ident] {S}
  x1 v x2 x3 x4 x5:
    ¬(x1 = x2) →
    (PortMap.getIO
      (Batteries.AssocList.cons x1 v
        (Batteries.AssocList.nil : PortMap Ident ((T : Type) × (S → T → S → Prop))))
      x2).snd x3 x4 x5 → False := by
  revert x2 x3 x4 x5
  generalize Hpm :
    (Batteries.AssocList.nil : PortMap Ident ((T : Type) × (S → T → S → Prop)))
    = pm
  intros x2 x3 x4 x5 Hneq Hsnd
  apply (getIO_cons_false pm x1 v x2 x3 x4 x5 Hneq (by rw [← Hpm]; simpa) Hsnd)

-- TODO: Move elsewhere
syntax (name := haveByLet) "have_hole " haveDecl : tactic
macro_rules
  | `(tactic| have_hole $id:ident $bs* : $type := $proof) =>
    `(tactic| (let h $bs* : $type := $proof; have $id:ident := h; clear h))

instance : MatchInterface (queue T₁) (bag T₁) where
  input_types := by
    intro ident; unfold queue bag; simp
    by_cases ({ inst := InstIdent.top, name := 0 }: InternalPort Nat) = ident
    <;> simpa [OfNat.ofNat, getIO_cons]
  output_types := by
    intro ident; unfold queue bag; simp
    by_cases H: ({ inst := InstIdent.top, name := 0 }: InternalPort Nat) = ident
    <;> simpa [*, drunfold, OfNat.ofNat, instOfNatInternalPortNat, instOfNatNat, getIO_cons]
  inputs_present := by intros; rfl
  outputs_present := by
    intros ident;
    unfold queue bag
    by_cases ({ inst := InstIdent.top, name := 0 }: InternalPort Nat) = ident
    <;> simpa [*, OfNat.ofNat, instOfNatInternalPortNat, instOfNatNat]

def φ (I S : List T₁) : Prop := I = S

theorem queue_refine_bag: queue T₁ ⊑_{φ} bag T₁ := by
  intro i s H; constructor
  · intros ident mid_i v Hrule; exists mid_i, mid_i; and_intros
    · unfold queue at *; dsimp at *
      by_cases ({ inst := InstIdent.top, name := 0 }: InternalPort Nat) = ident
      · subst ident;
        rw [rw_rule_execution] at Hrule; dsimp at Hrule
        subst mid_i;
        have_hole Hhole: ((bag T₁).inputs.getIO { inst := InstIdent.top, name := 0 }) = _ := by
          unfold bag; unfold OfNat.ofNat instOfNatInternalPortNat instOfNatNat;
          simp [drunfold]; rfl
        rw [rw_rule_execution Hhole]; dsimp; subst i; rfl
      · dsimp at v;
        exfalso
        rename_i Hneq
        apply (getIO_cons_nil_false _ _ ident)
        · exact Hneq
        · exact Hrule
    · constructor
    · rfl
  · intros ident mid_i v Hrule
    exists mid_i
    split_ands
    · unfold queue at *; dsimp at v Hrule;
      by_cases ({ inst := InstIdent.top, name := 0 }: InternalPort Nat) = ident
      · subst ident
        rw [rw_rule_execution] at Hrule; dsimp at *
        unfold bag; dsimp
        simp [*, OfNat.ofNat, instOfNatInternalPortNat, instOfNatNat, getIO_cons];
        rw [rw_rule_execution (h := by apply getIO_cons)]
        dsimp
        subst i; subst s
        exists (Fin.mk 0 (by simpa))
      · -- TODO: Exactly the same code as above, could be a tactic
        exfalso
        rename_i Hneq
        apply (getIO_cons_nil_false _ _ ident)
        · exact Hneq
        · exact Hrule
    · rfl
  · intros _ mid_i _ _; exists mid_i

end DataflowRewriter.BagQueue
