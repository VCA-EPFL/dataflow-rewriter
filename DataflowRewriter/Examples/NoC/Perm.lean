/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/
import Lean
import DataflowRewriter.Basic

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

elab "dr_perm_simp " l:term : tactic => Tactic.withMainContext do
  let goalType ← Lean.Elab.Tactic.getMainTarget
  match goalType with
  | .app (.app (.app (.const `List.Perm _) T) l₁) l₂ =>
    let tmp ← mkFreshExprMVar l₁
    Lean.logInfo f!"T:  {T}"
    Lean.logInfo f!"l₁: {l₁}"
    Lean.logInfo f!"l₂: {l₂}"
    let l ← Lean.Elab.Tactic.elabTerm l none -- TODO: Expected type: List T
    Lean.logInfo f!"l: {l}"
    -- TODO: We now have the two lists l₁ and l₂
    -- 1: Assert that l is of type List T ?
    -- 2: Put both l₁ and l₂ into normal form, while preserving the fact they
    -- are permutations of one another
    -- 3: If l is contained in both l₁ and l₂, remove it
  | _ => throwError s!"Goal is not a permutation"

theorem perm_append' : typeOf @perm_append := by
    dsimp
    intros α l l1 l2 l3
    apply Iff.intro <;> intros H
    skip
    · dr_perm_simp l
      sorry
    · dr_perm_simp l
      sorry
