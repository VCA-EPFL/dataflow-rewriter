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
import DataflowRewriter.ModuleReduction
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

variable (T₁ T₂ T₃) in
def_module lhsModule : StringModule (lhsModuleType T₁ T₂ T₃) := [e| (rewriteLhsRhs S₁ S₂ S₃).input_expr, @environmentLhs T₁ T₂ T₃ S₁ S₂ S₃ ]
reduction_by
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

#check (lhsModule T₁ T₂ T₃).internals

set_option maxHeartbeats 0 in
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
    dsimp [ExprLow.build_module_expr, rewriteLhsRhs, rewrite, rhs_extract, rhsLower, rhs, ExprHigh.extract, List.foldlM, toString]
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
| lhs: ∀ lower arb, partially_flushed ⟨lower, [], arb⟩
| rhs: ∀ lower arb, partially_flushed ⟨lower, arb, []⟩

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

theorem s' {T₁ T₂ T₃: Type _} (i i': rhsModuleType T₁ T₂ T₃) :
  ∀ rule, rule ∈ (rhsModule T₁ T₂ T₃).internals ∧ rule i i' → existSR (rhsModule T₁ T₂ T₃).internals i i' := by
    intro rule ⟨_, _⟩
    apply existSR.step i i' i' rule
    . assumption
    . assumption
    . exact existSR_reflexive

theorem lengthify {T₁: Type _} (a b: List T₁): a = b → a.length = b.length := by
  intro heq; rw [heq]

theorem takify {T₁: Type _} (l: ℕ) (l₁ l₂: List T₁): l₁ = l₂ -> List.take l l₁ = List.take l l₂ := by
  intro heq; rw [heq]

theorem dropify {T₁: Type _} (l: ℕ) (l₁ l₂: List T₁): l₁ = l₂ -> List.drop l l₁ = List.drop l l₂ := by
  intro heq; rw [heq]

theorem product_is_list_zip {T₁ T₂: Type _} (x: List (T₁ × T₂)): x = List.zip (List.map Prod.fst x) (List.map Prod.snd x) := by
  induction x with
  | nil => simp
  | cons head tail ih =>
    simp only [List.map_cons, List.zip_cons_cons, <- ih]

theorem append_iff {α} {a b c d : List α} : a.length = c.length → (a ++ b = c ++ d ↔ a = c ∧ b = d) := by
  intro lengths
  constructor
  . intro h
    and_intros
    . replace h := congrArg (List.take a.length) h
      rw [List.take_left, lengths, List.take_left] at h
      assumption
    . apply dropify a.length at h
      rw [List.drop_left, lengths, List.drop_left] at h
      assumption
  . intro ⟨_, _⟩; subst_vars; rfl

set_option maxHeartbeats 0 in
theorem refines {T: Type _} [DecidableEq T]: rhsModule T₁ T₂ T₃ ⊑_{φ} lhsModule T₁ T₂ T₃ := by
  unfold Module.refines_φ
  intro init_i init_s Hφ
  apply Module.comp_refines.mk
  -- input rules
  . intro ident i s a
    by_cases HContains: ((rhsModule T₁ T₂ T₃).inputs.contains ident)
    . obtain ⟨⟨sj2l, sj2r⟩, ⟨sj1l, sj1r⟩⟩ := init_s
      obtain ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ := init_i
      obtain ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ := i
      unfold rhsModule at HContains; simp at HContains

      rcases HContains with h | h | h
        <;> subst_vars <;> simp <;> rw [PortMap.rw_rule_execution] at a <;> simp at a
      . obtain ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ := a
        subst_vars
        have_hole heq : ((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_0" }).fst = _ := by simp [drunfold]; rfl
        -- We construct the almost_mid_s manually
        use ⟨⟨sj2l, sj2r⟩, ⟨sj1l ++ [heq.mp s], sj1r⟩⟩
        apply And.intro
        . -- verify that the rule holds
          rw [PortMap.rw_rule_execution (by simp[drunfold, lhsModule]; rfl)]
          simp
        . -- verify that the invariant holds when we flush the system
          obtain ⟨s', ⟨_, _⟩⟩ := something' ⟨⟨sj2l, sj2r⟩, sj1l ++ [heq.mp s], sj1r⟩ -- We flush the system to reach s'
          use s'
          apply And.intro
          . assumption
          . unfold φ at *
            apply And.intro
            . apply something _ (⟨sj2l, sj2r⟩, sj1l ++ [heq.mp s], sj1r) s'
              . obtain ⟨Hψ, _⟩ := Hφ
                unfold ψ at *; simp at *
                obtain ⟨_, _, _⟩ := Hψ
                subst_vars
                and_intros
                . simp only [<- List.append_assoc, List.append_left_inj]
                  assumption
                . assumption
                . rfl
              . assumption
            . assumption
      . obtain ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩, _⟩ := a
        subst_vars
        reduce at s
        use ⟨⟨sj2l, sj2r⟩, ⟨sj1l, sj1r ++ [s]⟩⟩
        apply And.intro
        . rw [PortMap.rw_rule_execution (by simp[drunfold, lhsModule]; rfl)]; simp
        . obtain ⟨s', ⟨_, _⟩⟩ := something' ⟨⟨sj2l, sj2r⟩, sj1l, sj1r ++ [s]⟩
          use s'
          apply And.intro
          . assumption
          . unfold φ at *
            apply And.intro
            . apply something _ (⟨sj2l, sj2r⟩, sj1l, sj1r ++ [s]) s'
              . obtain ⟨Hψ, _⟩ := Hφ
                unfold ψ at *; simp at *
                obtain ⟨_, _, _⟩ := Hψ
                subst_vars
                and_intros
                . assumption
                . simp only [<- List.append_assoc, List.append_left_inj] at *
                  assumption
                . rfl
              . assumption
            . assumption
      . obtain ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩, _⟩ := a
        subst_vars
        reduce at s
        use ⟨⟨sj2l, sj2r ++ [s]⟩, ⟨sj1l, sj1r⟩⟩
        apply And.intro
        . rw [PortMap.rw_rule_execution (by simp[drunfold, lhsModule]; rfl)]; simp
        . obtain ⟨s', ⟨_, _⟩⟩ := something' ⟨⟨sj2l, sj2r ++ [s]⟩, sj1l, sj1r⟩
          use s'
          apply And.intro
          . assumption
          . unfold φ at *
            apply And.intro
            . apply something _ (⟨sj2l, sj2r  ++ [s]⟩, sj1l, sj1r) s'
              . obtain ⟨Hψ, _⟩ := Hφ
                unfold ψ at *; simp at *
                obtain ⟨_, _, _⟩ := Hψ
                subst_vars
                and_intros
                . assumption
                . assumption
                . simp only [<- List.append_assoc, List.append_left_inj] at *
              . assumption
            . assumption
    . exfalso; exact (PortMap.getIO_not_contained_false a HContains)
  -- output rules
  . intro ident i v hrule
    by_cases HContains: ((rhsModule T₁ T₂ T₃).outputs.contains ident)
    · obtain ⟨⟨sj2l, sj2r⟩, ⟨sj1l, sj1r⟩⟩ := init_s
      obtain ⟨⟨ij2l, ij2r⟩, ⟨ij1l, ij1r⟩, ip⟩ := init_i
      obtain ⟨⟨ij2l', ij2r'⟩, ⟨ij1l', ij1r'⟩, ip'⟩ := i
      unfold rhsModule at HContains; simp at HContains
      rcases HContains with h <;> subst_vars
      <;> simp <;>
      rw [PortMap.rw_rule_execution (by simp [PortMap.getIO]; rfl)] at hrule <;>
      simp at hrule
      obtain ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ := hrule
      repeat cases ‹_∧_›
      subst_vars
      rename_i hlval hrval hpf
      dsimp at *
      rename_i htmp; cases htmp
      cases hpf
      · simp at hlval; simp at *
        rw [<- List.take_append_drop ij2l.length (List.map Prod.fst ij2r ++ ij1l)] at hrval
        --rw [<- List.append_assoc (List.map (Prod.snd ∘ Prod.fst) ip')] at hrval
        --rw [<- List.append.eq_2 _ _ ((List.map (Prod.snd ∘ Prod.fst) ip' ++ List.take ij2l.length (List.map Prod.fst ij2r' ++ ij1l'))] at hrval
        rw [show v.1.2 ::
            (List.map (Prod.snd ∘ Prod.fst) ip' ++
              (List.take ij2l.length (List.map Prod.fst ij2r ++ ij1l) ++
                List.drop ij2l.length (List.map Prod.fst ij2r ++ ij1l))) = v.1.2 ::
            (List.map (Prod.snd ∘ Prod.fst) ip' ++
              List.take ij2l.length (List.map Prod.fst ij2r ++ ij1l)) ++
                List.drop ij2l.length (List.map Prod.fst ij2r ++ ij1l) by simp] at hrval
        rw [append_iff] at hrval
        obtain ⟨hrvall, _⟩ := hrval
        . subst_vars
          apply Exists.intro ⟨ ⟨ _, _ ⟩, _, _ ⟩
          and_intros <;> dsimp
          · rewrite [product_is_list_zip sj2l, hlval, hrvall]; rfl
          · apply lengthify at hlval; simp at hlval
            apply lengthify at hrvall; simp [hlval, add_comm _ 1, add_right_inj, add_assoc] at hrvall
            rw [List.append_nil, <- List.zip_eq_zipWith, List.map_fst_zip]
            simp [hrvall] -- lia + assumption in context
          · apply lengthify at hlval; simp at hlval
            apply lengthify at hrvall; simp [hlval, add_comm _ 1, add_right_inj, add_assoc] at hrvall
            rewrite [<- List.zip_eq_zipWith, List.map_snd_zip]
            . simp only [List.append_assoc, List.take_append_drop]
            . simp only [List.length_append, List.length_map, List.length_take, add_le_add_iff_left, inf_le_left]
          · rewrite [List.append_assoc]; rfl
          · constructor
        . apply lengthify at hlval; simp at hlval
          apply lengthify at hrval; simp [hlval, add_comm _ 1, add_right_inj, add_assoc] at hrval
          simp only [hlval, List.length_map, List.length_cons, List.length_append, List.length_take,
            add_left_inj, add_right_inj, left_eq_inf] -- lengthify the goal
          simp only [le_iff_exists_add, <- hrval, add_right_inj, exists_eq'] -- lia
      . simp at hrval; simp at *
        rw [<- List.take_append_drop (ij2r.length + ij1l.length) ij2l] at hlval
        rw [show v.1.1 ::
            (List.map (Prod.fst ∘ Prod.fst) ip' ++
              (List.take (ij2r.length + ij1l.length) ij2l ++
                List.drop (ij2r.length + ij1l.length) ij2l)) = v.1.1 ::
            (List.map (Prod.fst ∘ Prod.fst) ip' ++
              List.take (ij2r.length + ij1l.length) ij2l) ++
                List.drop (ij2r.length + ij1l.length) ij2l by simp] at hlval
        rw [append_iff] at hlval
        obtain ⟨hlvall, hlvalr⟩ := hlval
        . subst_vars
          apply Exists.intro ⟨ ⟨ _, _ ⟩, _, _ ⟩
          . and_intros <;> dsimp
            . rewrite [product_is_list_zip sj2l, hrval, hlvall]; rfl
            . apply lengthify at hrval; simp at hrval
              apply lengthify at hlvall; simp [hrval, add_comm _ 1, add_right_inj, add_assoc] at hlvall
              simp [<- List.zip_eq_zipWith, List.map_fst_zip, hlvall]
            . apply lengthify at hrval; simp at hrval
              apply lengthify at hlvall; simp [hrval, add_comm _ 1, add_right_inj, add_assoc] at hlvall
              rewrite [<- List.zip_eq_zipWith, List.map_snd_zip]
              . simp
              . simp [hlvall]
            . simp
            . constructor
        . apply lengthify at hrval; simp [add_comm _ 1, add_right_inj, add_assoc] at hrval
          apply lengthify at hlval; simp [hrval, add_comm _ 1, add_left_inj, add_assoc] at hlval
          simp only [hrval, List.length_map, List.length_cons, add_comm _ 1, add_right_inj, List.length_append, List.length_take, left_eq_inf] -- lengthify the goal
          simp only [le_iff_exists_add, <- hlval, add_right_inj, exists_eq', add_assoc] -- lia
    . exfalso; exact (PortMap.getIO_not_contained_false hrule HContains)
  -- internal rules
  . intros rule mid_i _ _
    use init_s
    apply And.intro
    . exact existSR_reflexive
    . unfold φ at *
      obtain ⟨_, _⟩ := Hφ
      apply And.intro
      . apply (something'' init_i)
        . assumption
        . apply s' init_i mid_i rule
          and_intros <;> assumption
      . assumption


#print axioms refines

end DataflowRewriter.JoinRewrite
