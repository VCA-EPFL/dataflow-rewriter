/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Module
import Graphiti.Simp
import Graphiti.ExprHigh
import Graphiti.AssocList.Basic
import Graphiti.TypeExpr
import Graphiti.Environment

open Batteries (AssocList)

namespace Graphiti.CombModule

@[drunfold] def nand : NatModule (Option Bool × Option Bool) :=
  { inputs := [ (0, ⟨ Bool, λ s tt s' => s.1 = none ∧ s'.1 = .some tt ∧ s'.2 = s.2 ⟩)
              , (1, ⟨ Bool, λ s tt s' => s.2 = none ∧ s'.2 = .some tt ∧ s'.1 = s.1 ⟩)].toAssocList,
    outputs := [(0, ⟨ Bool, λ s tt s' => ∃ a b, s.1 = .some a ∧ s.2 = .some b ∧ tt = ¬ (a ∧ b) ∧ s' = (.none, .none) ⟩)].toAssocList
    init_state := λ s => s = default
  }

@[drunfold] def not : NatModule (Option Bool) :=
  { inputs := [(0, ⟨ Bool, λ s tt s' => s = none ∧ s' = .some tt ⟩)].toAssocList,
    outputs := [(0, ⟨ Bool, λ s tt s' => ∃ a, s = .some a ∧ tt = ¬ a ∧ s' = .none ⟩)].toAssocList
    init_state := λ s => s = default
  }

attribute [drcompute] Batteries.AssocList.toList Function.uncurry Module.mapIdent List.toAssocList List.foldl Option.pure_def Option.bind_eq_bind Option.bind_some Module.renamePorts Batteries.AssocList.mapKey InternalPort.map toString Nat.repr Nat.toDigits Nat.toDigitsCore Nat.digitChar List.asString Option.bind Batteries.AssocList.mapVal Batteries.AssocList.eraseAll Batteries.AssocList.eraseP beq_self_eq_true Option.getD cond beq_self_eq_true  beq_iff_eq  InternalPort.mk.injEq  String.reduceEq  and_false  imp_self BEq.beq AssocList.bijectivePortRenaming AssocList.keysList AssocList.eraseAllP List.inter

attribute [drdecide] InternalPort.mk.injEq and_false decide_False decide_True and_true Batteries.AssocList.eraseAllP  InternalPort.mk.injEq
  and_false  decide_False  decide_True  reduceCtorEq  cond  List.map List.elem_eq_mem List.mem_cons List.mem_singleton Bool.decide_or InternalPort.mk.injEq
  String.reduceEq and_false decide_false reduceCtorEq and_self Bool.or_self Bool.false_eq_true not_false_eq_true
  List.filter_cons_of_neg and_true List.filter_nil List.empty_eq decide_true List.nodup_cons List.not_mem_nil
  List.nodup_nil Bool.and_self reduceIte List.concat_eq_append dreduceIte List.append_nil

def connectNot' : NatModule (Option Bool) := by
  precomputeTac Module.connect' not 0 0 by
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq]
    conv =>
      pattern (occs := *) Module.connect'' _ _
      all_goals
        rw [(Module.connect''_dep_rw (h := by simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?]; rfl)
                                     (h' := by simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?]; rfl))]; rfl
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?,AssocList.filter,-Prod.exists]
    unfold Module.connect''
    dsimp

def connectNot : NatModule (Option Bool) := by
  precomputeTac ({connectNot' with inputs := [(0, ⟨Option Bool, fun st b st' => st = b ∧ st = st'⟩)].toAssocList} : NatModule (Option Bool)) by
    dsimp [connectNot']
    conv =>
      pattern (occs := *) And _ _
      all_goals
        simp; rfl

#print connectNot

end Graphiti.CombModule
