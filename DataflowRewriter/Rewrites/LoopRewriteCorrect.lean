/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.Rewrites.LoopRewrite
import DataflowRewriter.ExprLowLemmas
import Mathlib

namespace DataflowRewriter.LoopRewrite

open Batteries (AssocList)

open Lean hiding AssocList
open Meta Elab

open StringModule

section Proof

variable {Data : Type}
variable (DataS : String)
variable (f : Data → Data × Bool)

variable [Inhabited Data]

attribute [drcompute] Batteries.AssocList.toList Function.uncurry Module.mapIdent List.toAssocList List.foldl
  Option.pure_def Option.bind_eq_bind Option.bind_some Module.renamePorts
  Batteries.AssocList.mapKey InternalPort.map toString Nat.repr Nat.toDigits Nat.toDigitsCore Nat.digitChar
  List.asString Batteries.AssocList.mapVal Batteries.AssocList.eraseAll Batteries.AssocList.eraseP
  beq_self_eq_true Option.getD cond beq_self_eq_true  beq_iff_eq  InternalPort.mk.injEq  String.reduceEq and_false
  imp_self BEq.beq Module.bijectivePortRenaming ExprLow.filterId List.Nodup List.inter AssocList.keysList List.filter
  List.elem AssocList.eraseAllP

attribute [drdecide] InternalPort.mk.injEq and_false decide_False decide_True and_true Batteries.AssocList.eraseAllP
  InternalPort.mk.injEq
  and_false  decide_False  decide_True  reduceCtorEq  cond  List.map List.empty_eq decide_true ne_eq List.pairwise_cons
  List.mem_singleton forall_eq
  InternalPort.mk.injEq String.reduceEq and_false not_false_eq_true List.not_mem_nil IsEmpty.forall_iff
  implies_true List.Pairwise.nil and_self Bool.and_self reduceCtorEq reduceIte decide_false and_true
  List.remove List.get_eq_getElem eq_mp_eq_cast cast_eq Prod.exists forall_const not_true_eq_false imp_self
  List.append_nil

def rewriteLhsRhs := rewrite.rewrite [DataS] |>.get rfl

def environmentLhs : IdentMap String (TModule1 String) := lhs Data DataS f |>.snd

def environmentRhs : IdentMap String (TModule1 String) := rhs Data DataS f |>.snd

/--
info: ["branch T", "pure f", "mux T", "fork Bool 2", "init Bool false", "split T Bool", "bag T"]
-/
#guard_msgs in
#eval @environmentLhs Unit "T" (λ _ => default) _ |>.keysList

/--
info: ["pure f", "fork Bool 2", "merge T 2", "branch T", "split T Bool"]
-/
#guard_msgs in
#eval @environmentRhs Unit "T" (λ _ => default) _ |>.keysList

open Lean Meta Simp in
/-- Simplification procedure for decide expressions that tries to prove
    `decide x = true` or `decide x = false` using `rfl` -/
-- def decideSimproc : Simproc := fun e => do
--   match e with
--   | .app (.app (.const ``decide _) x) _ => do
--     -- Try to prove equality with true
--     return .done { expr := .const ``false [] }
--   | _ => return .continue

-- simproc decideSimproc_def (@decide _ _) := decideSimproc

-- #check String
-- theorem decide_simproc_theorem :
--   decide ("a" = "a") = false := by
--     simp only [decideSimproc_def]

@[drcompute] theorem find?_bag_data : (Batteries.AssocList.find? ("bag " ++ DataS) (environmentLhs DataS f)) = .some ⟨_, bag Data⟩ := by
  unfold environmentLhs lhs
  simp
  exists "bag " ++ DataS
  sorry

@[drcompute] theorem find?_init_data : (Batteries.AssocList.find? ("init Bool false") (environmentLhs DataS f)) = .some ⟨_, init Bool false⟩ := sorry
@[drcompute] theorem find?_branch_data : (Batteries.AssocList.find? ("branch " ++ DataS) (environmentLhs DataS f)) = .some ⟨_, branch Data⟩ := sorry
@[drcompute] theorem find?_pure_f : (Batteries.AssocList.find? ("pure f") (environmentLhs DataS f)) = .some ⟨_, pure f⟩ := sorry
@[drcompute] theorem find?_mux_data : (Batteries.AssocList.find? ("mux " ++ DataS) (environmentLhs DataS f)) = .some ⟨_, mux Data⟩ := sorry
@[drcompute] theorem find?_fork_bool : (Batteries.AssocList.find? ("fork Bool 2") (environmentLhs DataS f)) = .some ⟨_, fork Bool 2⟩ := sorry
@[drcompute] theorem find?_split_data : (Batteries.AssocList.find? ("split " ++ DataS ++ " Bool") (environmentLhs DataS f)) = .some ⟨_, split Data Bool⟩ := sorry

@[drcompute] theorem find?_branch_data2 : (Batteries.AssocList.find? ("branch " ++ DataS) (environmentRhs DataS f)) = .some ⟨_, branch Data⟩ := sorry
@[drcompute] theorem find?_pure_f2 : (Batteries.AssocList.find? ("pure f") (environmentRhs DataS f)) = .some ⟨_, pure f⟩ := sorry
@[drcompute] theorem find?_merge_data2 : (Batteries.AssocList.find? ("merge " ++ DataS ++ " 2") (environmentRhs DataS f)) = .some ⟨_, merge Data 2⟩ := sorry
@[drcompute] theorem find?_fork_bool2 : (Batteries.AssocList.find? ("fork Bool 2") (environmentRhs DataS f)) = .some ⟨_, fork Bool 2⟩ := sorry
@[drcompute] theorem find?_split_data2 : (Batteries.AssocList.find? ("split " ++ DataS ++ " Bool") (environmentRhs DataS f)) = .some ⟨_, split Data Bool⟩ := sorry

def lhsTypeEvaled : Type := by
  precomputeTac ([T| (rewriteLhsRhs DataS).input_expr, environmentLhs DataS f ]) by
    simp [drunfold,seval,drcompute,drdecide]
    -- rw [find?_bag_data,find?_init_data,find?_branch_data,find?_pure_f,find?_mux_data,find?_fork_bool,find?_split_data]
    -- simp

#eval [e|(DataflowRewriter.ExprLow.base
                      { input := Batteries.AssocList.cons
                                   { inst := DataflowRewriter.InstIdent.top, name := "in1" }
                                   { inst := DataflowRewriter.InstIdent.internal "bag", name := "in1" }
                                   (Batteries.AssocList.nil),
                        output := Batteries.AssocList.cons
                                    { inst := DataflowRewriter.InstIdent.top, name := "out1" }
                                    { inst := DataflowRewriter.InstIdent.top, name := "o_out" }
                                    (Batteries.AssocList.nil) }
                      "bag T"), environmentLhs "T" (λ _ => ((), true))].outputs.keysList

#eval ([e| (rewriteLhsRhs "T").input_expr, environmentLhs "T" (λ _ => ((), true)) ]).outputs.keysList

set_option maxHeartbeats 0 in
def lhsEvaled : Module String
            (List Data ×
              (List Bool × Bool) ×
                List (Data × Bool) ×
                  (List Data × List Bool) × (List Data × List Bool) × List Bool × List Data × List Data × List Bool) := by
  precomputeTac [e| (rewriteLhsRhs DataS).input_expr, environmentLhs DataS f ] by
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq]
    rw [find?_bag_data,find?_init_data,find?_branch_data,find?_pure_f,find?_mux_data,find?_fork_bool,find?_split_data]
    simp [-AssocList.find?_eq]
    unfold Module.liftR Module.liftL
    dsimp
    -- repeat
    --   conv in (Module.bijectivePortRenaming _ _) =>
    --     congr <;> simp +ground +autoUnfold [drunfold,-AssocList.find?_eq]
    --   conv in (Module.bijectivePortRenaming _ _) => simp [Module.bijectivePortRenaming, drunfold,-AssocList.find?_eq]
    conv =>
      pattern (occs := *) Module.connect'' _ _
      all_goals
        rw [(Module.connect''_dep_rw (h := by simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?]; rfl)
                                     (h' := by simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?]; rfl))]; rfl
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq]
    unfold Module.connect''
    dsimp
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?,AssocList.filter]


set_option maxHeartbeats 0 in
def rhsEvaled : Module String (List (Data × Bool) × (List Data × List Bool) × List Data × List Data × List Bool) := by
  precomputeTac [e| (rewriteLhsRhs DataS).output_expr, environmentRhs DataS f ] by
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq]
    rw [find?_branch_data2,find?_pure_f2,find?_split_data2,find?_merge_data2]
    simp [-AssocList.find?_eq]
    unfold Module.liftR Module.liftL
    dsimp
    conv =>
      pattern (occs := *) Module.connect'' _ _
      all_goals
        rw [(Module.connect''_dep_rw (h := by simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?]; rfl)
                                     (h' := by simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?]; rfl))]; rfl
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq]
    unfold Module.connect''
    dsimp
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?,AssocList.filter]

#print lhsEvaled

end Proof

end DataflowRewriter.LoopRewrite
