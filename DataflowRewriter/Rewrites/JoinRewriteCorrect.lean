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
import Mathlib.Tactic

open Batteries (AssocList)

open Lean hiding AssocList
open Meta Elab

namespace DataflowRewriter.JoinRewrite

open StringModule

attribute [drcompute] Batteries.AssocList.toList Function.uncurry Module.mapIdent List.toAssocList List.foldl Option.pure_def Option.bind_eq_bind Option.bind_some Module.renamePorts Batteries.AssocList.mapKey InternalPort.map toString Nat.repr Nat.toDigits Nat.toDigitsCore Nat.digitChar List.asString Option.bind Batteries.AssocList.mapVal Batteries.AssocList.eraseAll Batteries.AssocList.eraseP beq_self_eq_true Option.getD cond beq_self_eq_true  beq_iff_eq  InternalPort.mk.injEq  String.reduceEq  and_false  imp_self BEq.beq AssocList.bijectivePortRenaming AssocList.keysList AssocList.eraseAllP List.inter AssocList.invertible

attribute [drdecide] InternalPort.mk.injEq and_false decide_False decide_True and_true Batteries.AssocList.eraseAllP  InternalPort.mk.injEq
  and_false  decide_False  decide_True  reduceCtorEq  cond  List.map List.elem_eq_mem List.mem_cons List.mem_singleton Bool.decide_or InternalPort.mk.injEq
  String.reduceEq and_false decide_false reduceCtorEq and_self Bool.or_self Bool.false_eq_true not_false_eq_true
  List.filter_cons_of_neg and_true List.filter_nil List.empty_eq decide_true List.nodup_cons List.not_mem_nil
  List.nodup_nil Bool.and_self reduceIte List.concat_eq_append dreduceIte List.append_nil

abbrev Ident := Nat

-- abbrev S₁ := "S1"
-- abbrev S₂ := "S2"
-- abbrev S₃ := "S3"
variable {T₁ T₂ T₃ : Type}
variable (S₁ S₂ S₃ : String)

def lhsNames := ((rewrite.rewrite [S₁, S₂, S₃]).get rfl).input_expr.build_module_names
def rhsNames := ((rewrite.rewrite [S₁, S₂, S₃]).get rfl).output_expr.build_module_names

def rewriteLhsRhs := rewrite.rewrite [S₁, S₂, S₃] |>.get rfl

def environmentLhs : IdentMap String (TModule1 String) := lhs T₁ T₂ T₃ S₁ S₂ S₃ |>.snd
def environmentRhs : IdentMap String (TModule1 String) := rhs T₁ T₂ T₃ S₁ S₂ S₃ |>.snd

@[drcompute] theorem find?_join1_data : (Batteries.AssocList.find? ("join " ++ S₁ ++ " " ++ S₂) (@environmentLhs T₁ T₂ T₃ S₁ S₂ S₃)) = .some ⟨_, join T₁ T₂⟩ := by stop
  dsimp [environmentLhs, lhs]
  have : ("join (" ++ S₁ ++ " × " ++ S₂ ++ ") " ++ S₃ == "join " ++ S₁ ++ " " ++ S₂) = false := by
    sorry
  rw [Batteries.AssocList.find?.eq_2]; rw [this]; dsimp
  have : ("join " ++ S₁ ++ " " ++ S₂ == "join " ++ S₁ ++ " " ++ S₂) = true := by simp
  rw [Batteries.AssocList.find?.eq_2]; rw [this]

@[drcompute] theorem find?_join2_data : (Batteries.AssocList.find? ("join (" ++ S₁ ++ " × " ++ S₂ ++ ") " ++ S₃) (@environmentLhs T₁ T₂ T₃ S₁ S₂ S₃)) = .some ⟨_, join (T₁ × T₂) T₃⟩ := by stop
  dsimp [environmentLhs, lhs]
  have : ("join (" ++ S₁ ++ " × " ++ S₂ ++ ") " ++ S₃ == "join (" ++ S₁ ++ " × " ++ S₂ ++ ") " ++ S₃) = true := by simp
  rw [Batteries.AssocList.find?.eq_2]; rw [this]

@[drcompute] theorem find?_join1_data2 : (Batteries.AssocList.find? ("join " ++ S₂ ++ " " ++ S₃) (@environmentRhs T₁ T₂ T₃ S₁ S₂ S₃)) = .some ⟨_, join T₂ T₃⟩ := by stop
  dsimp [environmentRhs, rhs]
  have : (("join " ++ S₁ ++ " (" ++ S₂ ++ " × " ++ S₃ ++ ")") == "join " ++ S₂ ++ " " ++ S₃) = false := by
    sorry
  rw [Batteries.AssocList.find?.eq_2]; rw [this]; dsimp
  have : (s!"pure ({S₁}×({S₂}×{S₃})) (({S₁}×{S₂})×{S₃})" == "join " ++ S₂ ++ " " ++ S₃) = false := by sorry
  rw [Batteries.AssocList.find?.eq_2]; rw [this]; dsimp
  have : ("join " ++ S₂ ++ " " ++ S₃ == "join " ++ S₂ ++ " " ++ S₃) = true := by simp
  rw [Batteries.AssocList.find?.eq_2]; rw [this]

@[drcompute] theorem find?_join2_data2 : (Batteries.AssocList.find? ("join " ++ S₁ ++ " (" ++ S₂ ++ " × " ++ S₃ ++ ")") (@environmentRhs T₁ T₂ T₃ S₁ S₂ S₃)) = .some ⟨_, join T₁ (T₂ × T₃)⟩ := by stop
  dsimp [environmentRhs, rhs]
  have : (("join " ++ S₁ ++ " (" ++ S₂ ++ " × " ++ S₃ ++ ")") == ("join " ++ S₁ ++ " (" ++ S₂ ++ " × " ++ S₃ ++ ")")) = true := by simp
  rw [Batteries.AssocList.find?.eq_2]; rw [this]

@[drcompute] theorem find?_pure_data2 : (Batteries.AssocList.find? ("pure (" ++ S₁ ++ "×(" ++ S₂ ++ "×" ++ S₃ ++ ")) ((" ++ S₁ ++ "×" ++ S₂ ++ ")×" ++ S₃ ++ ")") (@environmentRhs T₁ T₂ T₃ S₁ S₂ S₃)) = .some ⟨_, pure λ ((a, b, c) : T₁ × (T₂ × T₃)) => ((a, b), c)⟩ := by stop
  dsimp [environmentRhs, rhs]
  have : (("join " ++ S₁ ++ " (" ++ S₂ ++ " × " ++ S₃ ++ ")") == s!"pure ({S₁}×({S₂}×{S₃})) (({S₁}×{S₂})×{S₃})") = false := by sorry
  rw [Batteries.AssocList.find?.eq_2]; rw [this]; dsimp
  have : (s!"pure ({S₁}×({S₂}×{S₃})) (({S₁}×{S₂})×{S₃})" == s!"pure ({S₁}×({S₂}×{S₃})) (({S₁}×{S₂})×{S₃})") = true := by simp
  rw [Batteries.AssocList.find?.eq_2]; rw [this]

variable (T₁ T₂ T₃) in
def lhsModuleType : Type := by
  precomputeTac [T| (rewriteLhsRhs S₁ S₂ S₃).input_expr, @environmentLhs T₁ T₂ T₃ S₁ S₂ S₃ ] by
    -- ExprHigh reduction
    dsimp [rewriteLhsRhs, rewrite, lhsLower, lhs_extract, lhs, ExprHigh.extract]
    dsimp [List.foldlM]
    simp (disch := simp) only [AssocList.find?_cons_eq, AssocList.find?_cons_neq]; dsimp
    simp
    -- Lowering reduction -> creates ExprLow
    dsimp [ExprHigh.lower, ExprHigh.lower', ExprHigh.uncurry]
    -- Unfold build_module
    dsimp [ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module']
    -- Reduce environment access
    simp only [find?_join1_data, find?_join2_data]; dsimp

def cast_module_type {α} {f : α → Type _} {s s' : Σ T, f T} (heq : s = s') : f s.1 = f s'.1 := by simp_all

theorem rw_opaque {f : Type _ → Type _} {s s' : Σ T, f T} (heq : s = s') : @Opaque (f s.fst) s.snd ↔ @Opaque (f s'.fst) s'.snd := by
  subst s; rfl

@[simp] theorem toString1 : toString 1 = "1" := rfl
@[simp] theorem toString2 : toString 2 = "2" := rfl
@[simp] theorem toString3 : toString 3 = "3" := rfl

attribute [drcompute] Option.some_bind
      Option.bind_some AssocList.foldl_eq AssocList.findEntryP?_eq
      List.partition_eq_filter_filter List.mem_cons List.not_mem_nil or_false not_or
      Bool.decide_and decide_not Batteries.AssocList.toList List.reverse_cons List.reverse_nil
      List.nil_append List.cons_append List.toAssocList List.foldl_cons
      PortMapping.empty_append PortMapping.append_elements AssocList.cons_append
      AssocList.nil_append List.foldl_nil InternalPort.mk.injEq reduceCtorEq String.reduceEq
      and_self decide_false Bool.false_eq_true not_false_eq_true List.find?_cons_of_neg
      decide_true List.find?_cons_of_pos Option.isSome_some Bool.and_self
      List.filter_cons_of_pos List.filter_nil Function.comp_apply Bool.not_true
      List.filter_cons_of_neg Option.get_some decide_not
      Bool.not_eq_eq_eq_not Bool.not_true decide_eq_false_iff_not ite_not AssocList.foldl_eq
      Batteries.AssocList.toList List.foldl_cons InternalPort.mk.injEq reduceCtorEq and_true
      String.reduceEq and_false List.foldl_nil AssocList.cons_append
      AssocList.nil_append beq_iff_eq not_false_eq_true
      BEq.rfl Option.map_some Option.getD_some
      List.concat_eq_append AssocList.eraseAll_cons_neq AssocList.eraseAll_cons_eq AssocList.eraseAll_nil
      AssocList.find?_cons_eq AssocList.find?_cons_neq PortMap.getIO

variable (T₁ T₂ T₃) in
@[drunfold] def lhsModule : StringModule (lhsModuleType T₁ T₂ T₃) := by
  precomputeTac [e| (rewriteLhsRhs S₁ S₂ S₃).input_expr, @environmentLhs T₁ T₂ T₃ S₁ S₂ S₃ ] by
    dsimp [ExprLow.build_module_expr, rewriteLhsRhs, rewrite, lhsLower, lhs_extract, lhs, ExprHigh.extract, List.foldlM]
    rw [rw_opaque (by simp (disch := simp) only [drcompute, ↓reduceIte]; rfl)]
    dsimp [ ExprHigh.lower, ExprHigh.lower', ExprHigh.uncurry
          , ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module']
    rw [rw_opaque (by simp (disch := simp) only [drcompute, ↓reduceIte]; rfl)]
    dsimp [join, NatModule.join, NatModule.stringify, Module.mapIdent, InternalPort.map, NatModule.stringify_input, NatModule.stringify_output, toString]
    dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, AssocList.bijectivePortRenaming, AssocList.invertible, AssocList.keysList, AssocList.inverse, AssocList.filterId, AssocList.filter, List.inter]; simp (disch := simp) only [drcompute, ↓reduceIte]
    dsimp [Module.product, Module.liftL, Module.liftR]
    dsimp [Module.connect']
    simp (disch := simp) only [drcompute, ↓reduceIte]
    conv =>
      pattern (occs := *) Module.connect'' _ _
      all_goals
        rw [(Module.connect''_dep_rw (h := by simp (disch := simp) only [AssocList.eraseAll_cons_neq,AssocList.eraseAll_cons_eq,AssocList.eraseAll_nil,PortMap.getIO,AssocList.find?_cons_eq,AssocList.find?_cons_neq]; dsimp)
                                 (h' := by simp (disch := simp) only [AssocList.eraseAll_cons_neq,AssocList.eraseAll_cons_eq,AssocList.eraseAll_nil,PortMap.getIO,AssocList.find?_cons_eq,AssocList.find?_cons_neq]; dsimp))]
    unfold Module.connect''
    dsimp

variable (T₁ T₂ T₃) in
def rhsModuleType : Type := by
  precomputeTac [T| (rewriteLhsRhs S₁ S₂ S₃).output_expr, @environmentRhs T₁ T₂ T₃ S₁ S₂ S₃ ] by
    -- ExprHigh reduction
    dsimp [rewriteLhsRhs, rewrite, rhsLower, rhs_extract, rhs, ExprHigh.extract, toString, List.foldlM]
    simp (disch := simp) only [AssocList.find?_cons_eq, AssocList.find?_cons_neq]; dsimp
    simp
    -- Lowering reduction -> creates ExprLow
    dsimp [ExprHigh.lower, ExprHigh.lower', ExprHigh.uncurry]
    -- Unfold build_module
    dsimp [ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module']
    -- Reduce environment access
    simp only [find?_join1_data2, find?_join2_data2, find?_pure_data2]; dsimp

theorem mapKey_cons {α β γ} {a b} {f : α → γ} {m : AssocList α β}:
  (m.cons a b).mapKey f = (m.mapKey f).cons (f a) b := rfl

theorem mapKey_nil {α β γ} {f : α → γ}:
  (@Batteries.AssocList.nil α β).mapKey f = .nil := rfl

theorem mapVal_cons {α β γ} {a b} {f : α → β → γ} {m : AssocList α β}:
  (m.cons a b).mapVal f = (m.mapVal f).cons a (f a b) := rfl

theorem mapVal_nil {α β γ} {f : α → β → γ}:
  (@Batteries.AssocList.nil α β).mapVal f = .nil := rfl

variable (T₁ T₂ T₃) in
@[drunfold] def rhsModule : StringModule (rhsModuleType T₁ T₂ T₃) := by
  precomputeTac [e| (rewriteLhsRhs S₁ S₂ S₃).output_expr, @environmentRhs T₁ T₂ T₃ S₁ S₂ S₃ ] by
    dsimp [ExprLow.build_module_expr, rewriteLhsRhs, rewrite, rhs_extract, rhsLower, rhs, ExprHigh.extract, List.foldlM]
    rw [rw_opaque (by simp (disch := simp) only [drcompute, ↓reduceIte]; rfl)]
    dsimp [ ExprHigh.lower, ExprHigh.lower', ExprHigh.uncurry
          , ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module']
    rw [rw_opaque (by simp only [find?_join1_data2, find?_join2_data2, find?_pure_data2]; rfl)]
    rw [rw_opaque (by simp (disch := simp) only [drcompute, ↓reduceIte]; rfl)]
    dsimp [StringModule.pure, NatModule.pure, join, NatModule.join, NatModule.stringify, Module.mapIdent, InternalPort.map, NatModule.stringify_input, NatModule.stringify_output, toString]
    dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, AssocList.bijectivePortRenaming, AssocList.invertible, AssocList.keysList, AssocList.inverse, AssocList.filterId, AssocList.filter, List.inter]; simp (disch := simp) only [drcompute, ↓reduceIte]
    dsimp [Module.product, Module.liftL, Module.liftR]
    dsimp [Module.connect']
    simp (disch := simp) only [AssocList.eraseAll_cons_neq,AssocList.eraseAll_cons_eq,AssocList.eraseAll_nil]
    -- simp (disch := simp) only [drcompute, ↓reduceIte]
    conv =>
      pattern (occs := *) Module.connect'' _ _
      all_goals
        rw [(Module.connect''_dep_rw (h := by simp (disch := simp) only [AssocList.eraseAll_cons_neq,AssocList.eraseAll_cons_eq,AssocList.eraseAll_nil,PortMap.getIO,AssocList.find?_cons_eq,AssocList.find?_cons_neq]; dsimp)
                                 (h' := by simp (disch := simp) only [AssocList.eraseAll_cons_neq,AssocList.eraseAll_cons_eq,AssocList.eraseAll_nil,PortMap.getIO,AssocList.find?_cons_eq,AssocList.find?_cons_neq]; dsimp))]
    unfold Module.connect''
    dsimp

attribute [dmod] Batteries.AssocList.find? BEq.beq

instance : MatchInterface (rhsModule T₁ T₂ T₃) (lhsModule T₁ T₂ T₃) where
  input_types := by stop
    intro ident;
    by_cases h : (Batteries.AssocList.contains ↑ident (rhsModule n T).inputs)
    · have h' := AssocList.keysInMap h; fin_cases h' <;> rfl
    · have h' := AssocList.keysNotInMap h; dsimp [drunfold, AssocList.keysList] at h' ⊢
      simp at h'; let ⟨ ha, hb, hc ⟩ := h'; clear h'
      simp only [Batteries.AssocList.find?_eq, Batteries.AssocList.toList]
      rcases ident with ⟨ i1, i2 ⟩;
      repeat (rw [List.find?_cons_of_neg]; rotate_left; simp; intros; subst_vars; solve_by_elim)
      rfl
  output_types := by stop
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

-- #reduce rhsNames
-- #reduce rhsModuleType

-- #reduce lhsNames
-- #reduce lhsModuleType

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

inductive partially

#reduce (lhsModule T₁ T₂ T₃)

inductive partially_flushed: lhsModuleType T₁ T₂ T₃ -> Prop where
| lhs: ∀ lower arb, partially_flushed ⟨lower, ⟨ [], arb ⟩ ⟩
| rhs: ∀ lower arb, partially_flushed ⟨lower, ⟨ arb, [] ⟩ ⟩

#print rhsModuleType

def ψ (rhs : rhsModuleType T₁ T₂ T₃) (lhs : lhsModuleType T₁ T₂ T₃) : Prop :=
  let ⟨⟨j2l, j2r⟩, ⟨j1l, j1r⟩⟩ := lhs
  let ⟨⟨j2l', j2r'⟩, ⟨⟨j1l', j1r'⟩, p⟩⟩ := rhs
  (j2l.map Prod.fst ++ j1l = p.map (Prod.fst ∘ Prod.fst) ++ j2l') ∧
  (j2l.map Prod.snd ++ j1r = p.map ((Prod.snd ∘ Prod.fst)) ++ j2r'.map Prod.fst ++ j1l') ∧
  (j2r = p.map Prod.snd ++ j2r'.map Prod.snd ++ j1r')


-- TODO: Can I write differently the lambda that extract the element from p's queue
def φ (rhs : rhsModuleType T₁ T₂ T₃) (lhs : lhsModuleType T₁ T₂ T₃) : Prop :=
  (ψ rhs lhs) ∧ (partially_flushed lhs)

-- loogle.lean-lang.org
theorem φ_indistinguishable :
  ∀ x y, φ x y → Module.indistinguishable (rhsModule T₁ T₂ T₃) (lhsModule T₁ T₂ T₃) x y := by
  intro ⟨⟨_, _⟩, ⟨⟨_, _⟩, _⟩⟩ ⟨⟨_, _⟩, ⟨_, _⟩⟩ Hφ
  constructor <;> intro ident ⟨⟨_, _⟩, ⟨⟨_, _⟩, _⟩⟩ v H
  . by_cases HContains: ((rhsModule T₁ T₂ T₃).inputs.contains ident)
    . unfold rhsModule lhsModule at *; simp at v H HContains; simp
      rcases HContains with h | h | h
      all_goals
        subst ident
        rw [PortMap.rw_rule_execution] at *
        apply Exists.intro ⟨ ⟨ _, _ ⟩, _, _ ⟩
        rw [PortMap.rw_rule_execution]
        unfold φ ψ at Hφ <;> simp at Hφ
        dsimp
        and_intros <;> rfl
    . exfalso; exact (PortMap.getIO_not_contained_false H HContains)
  . by_cases HContains: ((rhsModule T₁ T₂ T₃).outputs.contains ident)
    . unfold rhsModule lhsModule at *; simp at v H HContains; simp
      subst ident
      rw [PortMap.rw_rule_execution] at *
      simp at H
      repeat cases ‹_ ∧ _›
      subst_vars
      cases ‹partially_flushed _› <;> simp at *
      . rename_i left
        rw [List.map_eq_cons_iff] at left
        obtain ⟨ ⟨v'1, v'2⟩, j2lr, h1, h2, h3⟩ := left
        subst_vars
        obtain ⟨⟨v111, v112⟩, v12⟩ := v
        dsimp at *
        rename_i left
        rw [List.cons.injEq] at left
        repeat cases left
        subst_vars
        apply Exists.intro ⟨ ⟨ _, _ ⟩, _, _ ⟩
        rw [PortMap.rw_rule_execution]
        dsimp
        and_intros <;> try rfl
      . rename_i left
        rw [List.map_eq_cons_iff] at left
        obtain ⟨ ⟨v'1, v'2⟩, j2lr, h1, h2, h3⟩ := left
        subst_vars
        obtain ⟨⟨v111, v112⟩, v12⟩ := v
        dsimp at *
        rename_i left
        rw [List.cons.injEq] at left
        repeat cases left
        subst_vars
        apply Exists.intro ⟨ ⟨ _, _ ⟩, _, _ ⟩
        rw [PortMap.rw_rule_execution]
        dsimp
        and_intros <;> try rfl
    . exfalso; exact (PortMap.getIO_not_contained_false H HContains)

theorem something':
  ∀ s, ∃ s', existSR (lhsModule T₁ T₂ T₃).internals s s' ∧ partially_flushed s' := by
  intro ⟨⟨l1, l2⟩, ⟨l3, l4⟩⟩
  induction l3 generalizing l1 l2 l4 with
  | nil =>
    apply Exists.intro
    and_intros
    . apply existSR_reflexive
    . constructor
  | cons x xs ih =>
    cases l4
    . apply Exists.intro
      and_intros
      . apply existSR_reflexive
      . constructor
    . rename_i head tail
      specialize ih (l1 ++ [(x, head)]) l2 tail
      obtain ⟨ ⟨⟨_, _⟩, ⟨_, _⟩⟩, HExists, HPartiallyFlushed⟩ := ih
      apply Exists.intro ⟨ ⟨ _, _ ⟩, _, _ ⟩
      and_intros
      . apply existSR.step _ ⟨ ⟨ _, _ ⟩, _, _ ⟩ _
        . unfold lhsModule; simp
          rfl
        . repeat apply Exists.intro
          and_intros <;> rfl
        . apply HExists
      . assumption

theorem something:
  ∀ i s s', ψ i s → existSR (lhsModule T₁ T₂ T₃).internals s s' → ψ i s' := by
  intro ⟨⟨_, _⟩, ⟨⟨_, _⟩, _⟩⟩ s s' Hψ E
  induction E
  . assumption
  . rename_i init mid _ rule Hrule c _ Himpl
    apply Himpl; clear Himpl
    unfold lhsModule at Hrule; simp at Hrule
    subst_vars
    obtain ⟨_, _, _, _, _, _, _, _⟩ := c
    let ⟨⟨_, _⟩, ⟨_, _⟩⟩ := init
    let ⟨⟨_, _⟩, ⟨_, _⟩⟩ := mid
    rename_i a _ _ _ _ _ b; simp at a b
    obtain ⟨ ⟨_, _⟩, ⟨_, _⟩⟩ := a
    obtain ⟨ ⟨_, _⟩ , ⟨_, _⟩⟩ := b
    unfold ψ at *; simp at *
    subst_vars
    obtain ⟨ _, ⟨_, _⟩ ⟩ := Hψ
    simp; and_intros <;> assumption

theorem something'':
  ∀ i i' s, ψ i s → existSR (rhsModule T₁ T₂ T₃).internals i i' → ψ i' s := by
  intro i i' ⟨⟨_, _⟩, ⟨_, _⟩⟩ Hψ E
  induction E
  . assumption
  . rename_i init mid _ rule Hrule c _ Himpl
    apply Himpl; clear Himpl
    unfold rhsModule at Hrule; simp at Hrule
    cases Hrule <;> subst_vars
    . obtain ⟨_, _, _, _, _, _, _, ⟨⟨⟨_, _⟩, _⟩, _⟩, ⟨_, _⟩, _⟩ := c
      let ⟨⟨_, _⟩, ⟨_, _⟩⟩ := init
      let ⟨⟨_, _⟩, ⟨_, _⟩⟩ := mid
      unfold ψ at *; simp at *
      rename_i synth1 synth2;
      obtain ⟨_, _⟩ := synth1
      obtain ⟨_, _⟩ := synth2
      obtain ⟨_, _, _⟩ := Hψ
      and_intros <;> subst_vars <;> try simp
      . assumption
      . rename_i synth1 _ _ _ _ _ _
        rw [<- synth1]; subst_vars
        assumption
      . assumption
    . obtain ⟨_, _, _, _, _, _, _, _, ⟨⟨⟨_, _⟩, _⟩, ⟨⟨_, _⟩, _⟩⟩⟩ := c
      let ⟨⟨_, _⟩, ⟨_, _⟩⟩ := init
      let ⟨⟨_, _⟩, ⟨_, _⟩⟩ := mid
      unfold ψ at *; simp at *
      rename_i synth1 synth2;
      obtain ⟨_, _⟩ := synth1
      obtain ⟨_, _⟩ := synth2
      obtain ⟨_, _, _⟩ := Hψ
      and_intros <;> subst_vars <;> simp
      . assumption
      . assumption

theorem refines {T: Type _} [DecidableEq T]: rhsModule T₁ T₂ T₃ ⊑_{φ} lhsModule T₁ T₂ T₃ := by
  unfold Module.refines_φ
  intro init_i init_s Hφ
  apply Module.comp_refines.mk
  -- input rules
  . intro ident i s a

    by_cases HContains: ((rhsModule T₁ T₂ T₃).inputs.contains ident)
    . unfold rhsModule at HContains; simp at HContains
      rcases HContains with h | h | h <;> subst_vars <;> simp
      . rw [PortMap.rw_rule_execution] at a

        unfold rhsModule at s; simp at s

        unfold rhsModule lhsModule at *
        subst_vars; simp at *
        rw [PortMap.getIO] at *
        apply Exists.intro
        rw [PortMap.rw_rule_execution] at *
        simp at *
        and_intros
        . obtain ⟨ ⟨_, _⟩ , _⟩ := a
          subst_vars
          sorry
        . rfl
        . sorry
        sorry
      . sorry
      . sorry
    . exfalso; exact (PortMap.getIO_not_contained_false a HContains)
  -- output rules
  . intros ident mid_i v rhs
    by_cases HContains: ((rhsModule T₁ T₂ T₃).outputs.contains ident)
    . unfold rhsModule at HContains; simp at HContains; subst_vars
      rw [PortMap.rw_rule_execution] at rhs; simp at rhs
      obtain ⟨⟨_, _⟩, _⟩ := v
      obtain ⟨⟨_, _⟩, ⟨⟨_, _⟩, _⟩⟩ := init_i
      obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := init_s
      obtain ⟨⟨_, _⟩, ⟨⟨_, _⟩, _⟩⟩ := mid_i
      obtain ⟨⟨_, ⟨_, _⟩⟩, ⟨_, _⟩⟩ := rhs
      unfold φ at Hφ <;> obtain ⟨Hψ, pf⟩ := Hφ
      unfold ψ at Hψ; simp at Hψ
      obtain ⟨_, ⟨_, _⟩⟩ := Hψ
      simp at *; subst_vars
      cases pf <;> simp
      . apply Exists.intro ⟨⟨_, _⟩, ⟨_, _⟩⟩
        apply And.intro
        . unfold lhsModule; simp; rw [PortMap.rw_rule_execution] <;> sorry
        . sorry
      . sorry
    . exfalso; exact (PortMap.getIO_not_contained_false rhs HContains)
  -- internal rules
  . intros rule mid_i HruleIn Hrule
    unfold φ at Hφ <;> obtain ⟨ Hψ, _ ⟩ := Hφ
    use init_s
    apply And.intro
    . exact existSR_reflexive
    . unfold φ <;> apply And.intro
      . unfold rhsModule at HruleIn
        simp at HruleIn
        obtain ⟨_, _⟩ := HruleIn <;> subst_vars
        . obtain⟨_, _, _, _, _, _, _, ⟨⟨⟨_, _⟩, _⟩, _⟩, ⟨⟨_, _⟩, _⟩⟩ := Hrule
          obtain ⟨⟨_, _⟩, ⟨⟨_, _⟩, _⟩⟩ := init_i
          obtain ⟨⟨_, _⟩, ⟨⟨_, _⟩⟩⟩ := init_s
          . subst_vars
            obtain ⟨⟨_, _⟩, ⟨⟨_, _⟩, _⟩⟩ := mid_i
            unfold ψ at *; simp at *
            and_intros
            . rename_i synth1 synth2
              obtain ⟨_, _⟩ := synth1
              obtain ⟨_, _⟩ := synth2
              obtain ⟨_, ⟨_, _⟩⟩ := Hψ
              subst_vars
              assumption
            . rename_i synth1 synth2
              obtain ⟨_, _⟩ := synth1
              obtain ⟨⟨_, _⟩, _⟩ := synth2
              obtain ⟨_, ⟨_, _⟩⟩ := Hψ
              subst_vars <;> simp
              assumption
            . rename_i synth1 synth2
              obtain ⟨_, _⟩ := synth1
              obtain ⟨⟨_, _⟩, _⟩ := synth2
              obtain ⟨_, ⟨_, _⟩⟩ := Hψ
              subst_vars <;> simp
          . subst_vars
            obtain ⟨⟨_, _⟩, ⟨⟨_, _⟩, _⟩⟩ := mid_i
            unfold ψ at *; simp at *
            and_intros
            . rename_i synth1 synth2
              obtain ⟨_, _⟩ := synth1
              obtain ⟨⟨_, _⟩, _⟩ := synth2
              obtain ⟨_, ⟨_, _⟩⟩ := Hψ
              subst_vars <;> assumption
            . rename_i synth1 synth2
              obtain ⟨_, _⟩ := synth1
              obtain ⟨⟨_, _⟩, _⟩ := synth2
              obtain ⟨_, ⟨_, _⟩⟩ := Hψ
              subst_vars <;> simp
              assumption
            . rename_i synth1 synth2
              obtain ⟨_, _⟩ := synth1
              obtain ⟨⟨_, _⟩, _⟩ := synth2
              obtain ⟨_, ⟨_, _⟩⟩ := Hψ
              subst_vars <;> simp
        . obtain⟨_, _, _, _, _, _, _, _, ⟨⟨⟨_, _⟩, _⟩, ⟨⟨_, _⟩, _⟩⟩⟩ := Hrule
          obtain ⟨⟨_, _⟩, ⟨⟨_, _⟩, _⟩⟩ := init_i
          obtain ⟨⟨_, _⟩, ⟨⟨_, _⟩⟩⟩ := init_s
          . subst_vars
            obtain ⟨⟨_, _⟩, ⟨⟨_, _⟩, _⟩⟩ := mid_i
            unfold ψ at *; simp at *
            and_intros
            . rename_i synth1 synth2 synth3
              obtain ⟨_, _⟩ := synth1
              obtain ⟨_, _⟩ := synth2
              obtain ⟨⟨_, _⟩, _⟩ := synth3
              obtain ⟨_, ⟨_, _⟩⟩ := Hψ
              subst_vars <;> simp
              assumption
            . rename_i synth1 synth2 synth3
              obtain ⟨⟨_, _⟩, _⟩ := synth1
              obtain ⟨_, _⟩ := synth2
              obtain ⟨⟨_, _⟩, _⟩ := synth3
              obtain ⟨_, ⟨_, _⟩⟩ := Hψ
              subst_vars <;> simp
              assumption
            . rename_i synth1 synth2 synth3
              obtain ⟨⟨_, _⟩, _⟩ := synth1
              obtain ⟨_, _⟩ := synth2
              obtain ⟨⟨_, _⟩, _⟩ := synth3
              obtain ⟨_, ⟨_, _⟩⟩ := Hψ
              subst_vars <;> simp
          . subst_vars
            obtain ⟨⟨_, _⟩, ⟨⟨_, _⟩, _⟩⟩ := mid_i
            unfold ψ at *; simp at *
            and_intros
            . rename_i synth1 synth2 synth3
              obtain ⟨_, _⟩ := synth1
              obtain ⟨_, _⟩ := synth2
              obtain ⟨⟨_, _⟩, _⟩ := synth3
              obtain ⟨_, ⟨_, _⟩⟩ := Hψ
              subst_vars <;> simp
              assumption
            . rename_i synth1 synth2 synth3
              obtain ⟨⟨_, _⟩, _⟩ := synth1
              obtain ⟨_, _⟩ := synth2
              obtain ⟨⟨_, _⟩, _⟩ := synth3
              obtain ⟨_, ⟨_, _⟩⟩ := Hψ
              subst_vars <;> simp
              assumption
            . rename_i synth1 synth2 synth3
              obtain ⟨⟨_, _⟩, _⟩ := synth1
              obtain ⟨_, _⟩ := synth2
              obtain ⟨⟨_, _⟩, _⟩ := synth3
              obtain ⟨_, ⟨_, _⟩⟩ := Hψ
              subst_vars <;> simp
      . assumption


end DataflowRewriter.JoinRewrite
