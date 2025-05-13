/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/
import Lean
import DataflowRewriter.Basic
import Qq

open Lean Meta Elab

-- aesop -----------------------------------------------------------------------

@[simp] abbrev typeOf {α} (_ : α) := α

theorem perm_eraseIdx {α} {v} {l₁ l₂ : List α} {idx : Fin l₁.length} (Heq : l₁[idx] = v := by simpa):
  l₁[idx] = v → List.Perm l₁ (l₂ ++ [v]) ↔ List.Perm (List.eraseIdx l₁ idx) l₂ :=
  by sorry

-- theorem append_cons {α} {v} {l : List α} : v :: l = [v] ++ l := by rfl

theorem tmp_perm_r {α} {l₁ l₂ : List α} :
  ∀ l, l₁.Perm l₂ → (l ++ l₁).Perm (l ++ l₂) := by
  intros l H; rwa [List.perm_append_left_iff]

theorem tmp_perm_l {α} {l₁ l₂ : List α} :
  ∀ l, l₁.Perm l₂ → (l₁ ++ l).Perm (l₂ ++ l) := by
    intros l H; rwa [List.perm_append_right_iff]

theorem tmp_perm_comm {α} {l₁ l₂ : List α} :
    l₁.Perm l₂ -> l₂.Perm l₁ := by sorry

theorem tmp_perm_append_comm_r {α} {l l₁ l₂ : List α} :
  l.Perm (l₁ ++ l₂) → l.Perm (l₂ ++ l₁) := by
    sorry

theorem tmp_perm_append_comm_l {α} {l l₁ l₂ : List α} :
  (l₁ ++ l₂).Perm l → (l₂ ++ l₁).Perm l := by
    sorry

theorem tmp_perm_append_assoc_l {α} {l l₁ l₂ l₃ : List α} :
  (l₁ ++ (l₂ ++ l₃)).Perm l → ((l₁ ++ l₂) ++ l₃).Perm l := by
    sorry

theorem tmp_perm_append_assoc_r {α} {l l₁ l₂ l₃ : List α} :
  l.Perm (l₁ ++ (l₂ ++ l₃)) → l.Perm ((l₁ ++ l₂) ++ l₃) := by
    sorry

theorem tmp_perm_append_left_fwd {α} {l l₁ l₂ : List α} :
  (l ++ l₁).Perm (l ++ l₂) → l₁.Perm l₂ := by
    sorry

theorem tmp_perm_append_right_fwd {α} {l l₁ l₂ : List α} :
  (l₁ ++ l).Perm (l₂ ++ l) → l₁.Perm l₂ := by
    sorry

theorem tmp_perm_append_rot_rl {α} {l l₁ l₂ l₃ : List α} :
  l.Perm (l₁ ++ (l₂ ++ l₃)) → l.Perm (l₂ ++ l₃ ++ l₁) := by sorry

theorem tmp_perm_append_rot_rr {α} {l l₁ l₂ l₃ : List α} :
  l.Perm (l₁ ++ (l₂ ++ l₃)) → l.Perm (l₃ ++ l₁ ++ l₂) := by sorry

attribute [aesop safe apply (rule_sets := [drperm])]
  tmp_perm_r
  tmp_perm_l
  List.Perm.refl

attribute [aesop safe forward (rule_sets := [drperm])]
  tmp_perm_comm
  tmp_perm_append_assoc_l
  tmp_perm_append_assoc_r
  tmp_perm_append_comm_l
  tmp_perm_append_comm_r
  tmp_perm_append_left_fwd
  tmp_perm_append_right_fwd

attribute [aesop 50% apply (rule_sets := [drperm])]
  -- tmp_perm_append_assoc_r1
  tmp_perm_append_assoc_l
  tmp_perm_append_assoc_r
  -- tmp_perm_append_assoc_l1
  -- tmp_perm_append_assoc_l2
  -- tmp_perm_append_comm_l
  tmp_perm_append_comm_l
  tmp_perm_append_comm_r
  tmp_perm_append_rot_rl
  tmp_perm_append_rot_rr

attribute [aesop 10% apply (rule_sets := [drperm])]
  tmp_perm_comm

-- attribute [aesop unsafe 25% (rule_sets := [drperm])]
--   List.append_assoc             -- Is this really useful with append_comm_assoc?
--   List.perm_append_comm         -- Is this really useful?
--   List.perm_append_comm_assoc   -- Is this really useful?
--   tmp_perm_append_assoc_r1
--   tmp_perm_append_assoc_r2
--   tmp_perm_append_assoc_l1
--   tmp_perm_append_assoc_l2
--   tmp_perm_append_comm_l
--   tmp_perm_append_comm_r
  -- tmp_perm_simp_l

-- attribute [aesop unsafe 10% (rule_sets := [drperm])]
--   List.perm_comm        -- Probably never useful?
  -- tmp_perm_append_comm

-- attribute [aesop 1% (rule_sets := [drperm])]
--   List.Perm.trans

macro "dr_perm_aesop" : tactic =>
  `(tactic|aesop?
    (rule_sets := [drperm, -default, -builtin])
    (config := {
          useSimpAll              := false,
          enableSimp              := false,
          maxRuleApplications     := 400,
          maxRuleApplicationDepth := 125,
  }))

theorem perm_append {α} {l l1 l2 l3 : List α} :
  l1.Perm (l2 ++ l3) <-> (l1 ++ l).Perm (l2 ++ l ++ l3) := by
    apply Iff.intro <;> intros _ <;> dr_perm_aesop
    · apply tmp_perm_append_rot_rr
      apply tmp_perm_comm
      apply tmp_perm_append_comm_r
      apply tmp_perm_r
      assumption
      skip
    · sorry

-- Proper tactic ---------------------------------------------------------------

theorem swap_l {α} (l₁ l₂ l : List α) : (l₂ ++ l₁).Perm l → (l₁ ++ l₂).Perm l
:= by sorry

theorem swap_r {α} (l₁ l₂ l : List α) : l.Perm (l₂ ++ l₁) → l.Perm (l₁ ++ l₂)
:= by sorry

open Qq

def put_front_l (T : Q(Type)) (fuel : Nat) (l ll : Q(List $T)) := Tactic.withMainContext do
  match fuel with
  | n + 1 =>
      Lean.logInfo m!"fuel = {n} with l = {l} and l' = {ll}"
      match ll with
      | ~q($l₁ ++ _) =>
          if l₁ == l then Lean.logInfo "left ok, done"
          else
            Lean.logInfo "yes"
            Tactic.evalTactic (←`(tactic| apply swap_l))
            Tactic.evalTactic (←`(tactic| ac_nf0))
            -- TODO: Probably l' need to be updated?
            put_front_l T n l ll
      | _ => Lean.logInfo m!"no, ll = {ll}"
  | 0 => Tactic.evalTactic (←`(tactic| skip))

elab "dr_perm_put_in_front " l:term : tactic => Tactic.withMainContext do
  Tactic.evalTactic (←`(tactic| ac_nf0))
  let goalType : Q(Prop) ← Lean.Elab.Tactic.getMainTarget
  match goalType with
    -- TODO: Do we need Tactic.withMainContext here ?
  | ~q(@List.Perm $T $ll $lr) => Tactic.withMainContext do
    let l ← Tactic.elabTermEnsuringType l q(List $T) -- same as (←mkAppM ``List #[T])
    let T ← instantiateMVars T
    let ll : Q(List $T) ← instantiateMVars ll
    let lr : Q(List $T) ← instantiateMVars lr
    let l : Q(List $T) ← instantiateMVars l
    Lean.logInfo m!"T:  {T}"
    Lean.logInfo m!"ll: {ll}"
    Lean.logInfo m!"lr: {lr}"
    Lean.logInfo m!"l: {l}"
    put_front_l T 10 l ll
    -- put_front_r T 10 l lr
  | _ => throwError s!"Goal is not a permutation"

theorem perm_append' : typeOf @perm_append := by
    dsimp
    intros α l l1 l2 l3
    apply Iff.intro <;> intros H <;>
    skip
    · ac_nf0
      dr_perm_put_in_front l
      sorry
    · sorry
