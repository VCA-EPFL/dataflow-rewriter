/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Lean
import Init.Data.BitVec.Lemmas
import Qq

import DataflowRewriter.Simp
import DataflowRewriter.Module
import DataflowRewriter.ExprLow
import DataflowRewriter.Component
import DataflowRewriter.KernelRefl
import DataflowRewriter.Reduce
import DataflowRewriter.List
import DataflowRewriter.ExprHighLemmas
import DataflowRewriter.Tactic
import DataflowRewriter.Rewrites.JoinRewrite

open Batteries (AssocList)

open Lean hiding AssocList
open Meta Elab

namespace DataflowRewriter.JoinRewrite

attribute [drcompute] Batteries.AssocList.toList Function.uncurry Module.mapIdent List.toAssocList List.foldl Batteries.AssocList.find? Option.pure_def Option.bind_eq_bind Option.bind_some Module.renamePorts Batteries.AssocList.mapKey InternalPort.map toString Nat.repr Nat.toDigits Nat.toDigitsCore Nat.digitChar List.asString Option.bind Batteries.AssocList.mapVal Batteries.AssocList.eraseAll Batteries.AssocList.eraseP beq_self_eq_true Option.getD cond beq_self_eq_true  beq_iff_eq  InternalPort.mk.injEq  String.reduceEq  and_false  imp_self BEq.beq Module.bijectivePortRenaming AssocList.keysList AssocList.eraseAllP List.inter

attribute [drdecide] InternalPort.mk.injEq and_false decide_False decide_True and_true Batteries.AssocList.eraseAllP  InternalPort.mk.injEq
  and_false  decide_False  decide_True  reduceCtorEq  cond  List.map List.elem_eq_mem List.mem_cons List.mem_singleton Bool.decide_or InternalPort.mk.injEq
  String.reduceEq and_false decide_false reduceCtorEq and_self Bool.or_self Bool.false_eq_true not_false_eq_true
  List.filter_cons_of_neg and_true List.filter_nil List.empty_eq decide_true List.nodup_cons List.not_mem_nil
  List.nodup_nil Bool.and_self reduceIte List.concat_eq_append dreduceIte List.append_nil

abbrev Ident := Nat

def ε ( n : Nat) ( T : Type _) : IdentMap String (TModule String) :=
  [ ("FixedSize.join", ⟨ _, StringModule.FixedSize.join T T n⟩)
  , ("FixedSize.joinP", ⟨ _, StringModule.FixedSize.join T (T × T) n⟩)
  , ("FixedSize.joinL", ⟨ _, StringModule.FixedSize.joinL T T T n⟩)
  ].toAssocList

def lhsNames := rewrite.input_expr.build_module_names
def rhsNames := rewrite.output_expr.build_module_names

def lhsModuleType ( n : Nat)  ( T : Type _) : Type := by
  precomputeTac [T| rewrite.input_expr, ε n T ] by
    dsimp only [drunfold,seval,drcompute]

@[drunfold] def lhsModule ( n : Nat)  ( T : Type _) : StringModule (lhsModuleType n T) := by
  precomputeTac [e| rewrite.input_expr, ε n T ] by
    simp [drunfold,seval,drcompute,drdecide]
    conv in Module.connect'' _ _ => rw [Module.connect''_dep_rw]; rfl
    unfold Module.connect''
    dsimp

def rhsModuleType ( n : Nat)  (T : Type _) : Type := by
  precomputeTac [T| rewrite.output_expr, ε n T ] by
    dsimp only [drunfold,seval,drcompute]

-- #reduce rhsNames
-- #reduce rhsModuleType

@[drunfold] def rhsModule ( n : Nat) (T : Type _) : StringModule (rhsModuleType n T) := by
  precomputeTac [e| rewrite.output_expr, ε n T ] by
    dsimp only [drunfold,seval,drcompute]
    simp only [seval,drdecide]
    conv in Module.connect'' _ _ => rw [Module.connect''_dep_rw]; rfl
    unfold Module.connect''
    dsimp

attribute [dmod] Batteries.AssocList.find? BEq.beq

instance {n T} : MatchInterface (rhsModule n T) (lhsModule n T) where
  input_types := by
    intro ident;
    by_cases h : (Batteries.AssocList.contains ↑ident (rhsModule n T).inputs)
    · have h' := AssocList.keysInMap h; fin_cases h' <;> rfl
    · have h' := AssocList.keysNotInMap h; dsimp [drunfold, AssocList.keysList] at h' ⊢
      simp at h'; let ⟨ ha, hb, hc ⟩ := h'; clear h'
      simp only [Batteries.AssocList.find?_eq, Batteries.AssocList.toList]
      rcases ident with ⟨ i1, i2 ⟩;
      repeat (rw [List.find?_cons_of_neg]; rotate_left; simp; intros; subst_vars; solve_by_elim)
      rfl
  output_types := by
    intro ident;
    by_cases h : (Batteries.AssocList.contains ↑ident (rhsModule n T).outputs)
    · have h' := AssocList.keysInMap h; fin_cases h' <;> rfl
    · have h' := AssocList.keysNotInMap h; dsimp [drunfold, AssocList.keysList] at h' ⊢
      simp at h'
      simp only [Batteries.AssocList.find?_eq, Batteries.AssocList.toList]
      rcases ident with ⟨ i1, i2 ⟩;
      repeat (rw [List.find?_cons_of_neg]; rotate_left; simp; intros; subst_vars; solve_by_elim)
      rfl
  inputs_present := by sorry
  outputs_present := by sorry


#reduce rhsNames
#reduce rhsModuleType

#reduce lhsNames
#reduce lhsModuleType

@[reducible] def cast_first {β : Type _ → Type _} {a b : (Σ α, β α)} (h : a = b) : a.fst = b.fst := by
  subst_vars; rfl

theorem sigma_rw {S T : Type _} {m m' : Σ (y : Type _), S → y → T → Prop} {x : S} {y : T} {v : m.fst}
        (h : m = m' := by reduce; rfl) :
  m.snd x v y ↔ m'.snd x ((cast_first h).mp v) y := by
  constructor <;> (intros; subst h; assumption)

theorem sigma_rw_simp {S T : Type _} {m m' : Σ (y : Type _), S → y → T → Prop} {x : S} {y : T} {v : m.fst}
        (h : m = m' := by simp [drunfold,drcompute,seval]; rfl) :
  m.snd x v y ↔ m'.snd x ((cast_first h).mp v) y := by
  constructor <;> (intros; subst h; assumption)

end DataflowRewriter.JoinRewrite
