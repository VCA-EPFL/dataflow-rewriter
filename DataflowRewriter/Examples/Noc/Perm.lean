/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/
import Lean
import DataflowRewriter.Basic
import Qq

open Lean Meta Elab

@[simp] abbrev typeOf {α} (_ : α) := α

-- aesop -----------------------------------------------------------------------

theorem perm_eraseIdx {α} {v} {l₁ l₂ : List α} {idx : Fin l₁.length} (Heq : l₁[idx] = v := by simpa):
  l₁[idx] = v → List.Perm l₁ (l₂ ++ [v]) ↔ List.Perm (List.eraseIdx l₁ idx) l₂ :=
  by sorry

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

macro "dr_perm_aesop" : tactic =>
  `(tactic|aesop
    (rule_sets := [drperm, -default])
    (config := {
          useSimpAll              := false,
          enableSimp              := false,
          maxRuleApplications     := 400,
          maxRuleApplicationDepth := 125,
  }))

-- Proper tactic ---------------------------------------------------------------

theorem swap_l {α} (l₁ l₂ l : List α) : (l₂ ++ l₁).Perm l → (l₁ ++ l₂).Perm l
:= by sorry

theorem swap_r {α} (l₁ l₂ l : List α) : l.Perm (l₂ ++ l₁) → l.Perm (l₁ ++ l₂)
:= by sorry

theorem perm_append' {α} (ll₁ ll₂ lr₁ lr₂ : List α) (H : ll₁.Perm lr₁) :
  ll₂.Perm lr₂ → (ll₁ ++ ll₂).Perm (lr₁ ++ lr₂) := by
    intros H' <;> exact List.Perm.append H H'

open Qq in
def perm_get_goal : Tactic.TacticM (Expr × Expr) := Tactic.withMainContext do
  Tactic.evalTactic (←`(tactic| ac_nf0))
  let goalType : Q(Prop) ← Lean.Elab.Tactic.getMainTarget
  match goalType with
  | ~q(@List.Perm $T $ll $lr) =>
    let u ← Meta.mkFreshLevelMVar
    let T : Q(Type $u) ← instantiateMVars T
    let ll : Q(List $T) ← instantiateMVars ll
    let lr : Q(List $T) ← instantiateMVars lr
    return (ll, lr)
  | _ => throwError s!"Goal is not a permutation"

def put_front_l (fuel : Nat) (l ll : Expr) := Tactic.withMainContext do
  match fuel with
  | 0 => Tactic.evalTactic (←`(tactic| skip))
  | n + 1 =>
      match Expr.getAppFn ll with
      | .const `HAppend.hAppend _ =>
        let args := Expr.getAppArgsN ll 5
        let hd := args[3]!
        let tl := args[4]!
        if hd != l then
          Tactic.evalTactic (←`(tactic| apply swap_l))
          let (ll, _) ← perm_get_goal
          put_front_l n l ll
      | _ => return

def put_front_r (fuel : Nat) (l lr : Expr) := Tactic.withMainContext do
  match fuel with
  | 0 => Tactic.evalTactic (←`(tactic| skip))
  | n + 1 =>
      match Expr.getAppFn lr with
      | .const `HAppend.hAppend _ =>
        let args := Expr.getAppArgsN lr 5
        let hd := args[3]!
        let tl := args[4]!
        if hd != l then
          Tactic.evalTactic (←`(tactic| apply swap_r))
          let (_, lr) ← perm_get_goal
          put_front_r n l lr
      | _ => return

elab "dr_perm_put_in_front " l:term : tactic => Tactic.withMainContext do
  let l ← Tactic.elabTerm l .none
  let (ll, lr) ← perm_get_goal
  -- TODO: Instead of 10, this should be List.length ll
  put_front_l 10 l ll
  put_front_r 10 l lr

-- TODO: dr_perm_put_in_front should also be usable on an hypothesis

-- TODO: dr_perm_simp:
-- For every element of left list, try to put them at the front and simplify

-- TODO: dr_put_in_shape: Take a list of list as an argument and try to re-order
-- both side to match (Just make a bunch of call to put_in_front but backward)

theorem test_dr_perm {α: Type} {l l1 l2 l3 : List α} :
  l1.Perm (l2 ++ l3) <-> (l1 ++ l).Perm (l2 ++ l ++ l3) := by
    apply Iff.intro <;> intros H
    · dr_perm_put_in_front l
      apply perm_append' (H := by apply List.Perm.rfl)
      dr_perm_aesop
    · sorry
