/-
Copyright (c) 2024-2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Hamza Remmal
-/

import Lean
import Init.Data.BitVec.Lemmas
import Qq

import DataflowRewriter.Simp
import DataflowRewriter.Module
import DataflowRewriter.FlushedModule
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

abbrev ExtRule (S: Type _) := (Σ T: Type _, S → T → S → Prop)
abbrev IntRule (S: Type _) := S → S → Prop

-- abbrev S₁ := "S1"
-- abbrev S₂ := "S2"
-- abbrev S₃ := "S3"
variable {T₁ T₂ T₃ : Type}
variable (S₁ S₂ S₃ : String)

@[drunfold_defs]
def lhsNames := ((rewrite.rewrite [S₁, S₂, S₃]).get rfl).input_expr.build_module_names
@[drunfold_defs]
def rhsNames := ((rewrite.rewrite [S₁, S₂, S₃]).get rfl).output_expr.build_module_names

@[drunfold_defs]
def rewriteLhsRhs := rewrite.rewrite [S₁, S₂, S₃] |>.get rfl

def environmentLhs : IdentMap String (TModule1 String) := lhs T₁ T₂ T₃ S₁ S₂ S₃ |>.snd
def environmentRhs : IdentMap String (TModule1 String) := rhs T₁ T₂ T₃ S₁ S₂ S₃ |>.snd

@[drenv] theorem find?_join1_data : (Batteries.AssocList.find? ("join " ++ S₁ ++ " " ++ S₂) (@environmentLhs T₁ T₂ T₃ S₁ S₂ S₃)) = .some ⟨_, join T₁ T₂⟩ := by stop
  dsimp [environmentLhs, lhs]
  have : ("join (" ++ S₁ ++ " × " ++ S₂ ++ ") " ++ S₃ == "join " ++ S₁ ++ " " ++ S₂) = false := by
    sorry
  rw [Batteries.AssocList.find?.eq_2]; rw [this]; dsimp
  have : ("join " ++ S₁ ++ " " ++ S₂ == "join " ++ S₁ ++ " " ++ S₂) = true := by simp
  rw [Batteries.AssocList.find?.eq_2]; rw [this]

@[drenv] theorem find?_join2_data : (Batteries.AssocList.find? ("join (" ++ S₁ ++ " × " ++ S₂ ++ ") " ++ S₃) (@environmentLhs T₁ T₂ T₃ S₁ S₂ S₃)) = .some ⟨_, join (T₁ × T₂) T₃⟩ := by stop
  dsimp [environmentLhs, lhs]
  have : ("join (" ++ S₁ ++ " × " ++ S₂ ++ ") " ++ S₃ == "join (" ++ S₁ ++ " × " ++ S₂ ++ ") " ++ S₃) = true := by simp
  rw [Batteries.AssocList.find?.eq_2]; rw [this]

@[drenv] theorem find?_join1_data2 : (Batteries.AssocList.find? ("join " ++ S₂ ++ " " ++ S₃) (@environmentRhs T₁ T₂ T₃ S₁ S₂ S₃)) = .some ⟨_, join T₂ T₃⟩ := by stop
  dsimp [environmentRhs, rhs]
  have : (("join " ++ S₁ ++ " (" ++ S₂ ++ " × " ++ S₃ ++ ")") == "join " ++ S₂ ++ " " ++ S₃) = false := by
    sorry
  rw [Batteries.AssocList.find?.eq_2]; rw [this]; dsimp
  have : (s!"pure ({S₁}×({S₂}×{S₃})) (({S₁}×{S₂})×{S₃})" == "join " ++ S₂ ++ " " ++ S₃) = false := by sorry
  rw [Batteries.AssocList.find?.eq_2]; rw [this]; dsimp
  have : ("join " ++ S₂ ++ " " ++ S₃ == "join " ++ S₂ ++ " " ++ S₃) = true := by simp
  rw [Batteries.AssocList.find?.eq_2]; rw [this]

@[drenv] theorem find?_join2_data2 : (Batteries.AssocList.find? ("join " ++ S₁ ++ " (" ++ S₂ ++ " × " ++ S₃ ++ ")") (@environmentRhs T₁ T₂ T₃ S₁ S₂ S₃)) = .some ⟨_, join T₁ (T₂ × T₃)⟩ := by stop
  dsimp [environmentRhs, rhs]
  have : (("join " ++ S₁ ++ " (" ++ S₂ ++ " × " ++ S₃ ++ ")") == ("join " ++ S₁ ++ " (" ++ S₂ ++ " × " ++ S₃ ++ ")")) = true := by simp
  rw [Batteries.AssocList.find?.eq_2]; rw [this]

@[drenv] theorem find?_pure_data2 : (Batteries.AssocList.find? ("pure (" ++ S₁ ++ "×(" ++ S₂ ++ "×" ++ S₃ ++ ")) ((" ++ S₁ ++ "×" ++ S₂ ++ ")×" ++ S₃ ++ ")") (@environmentRhs T₁ T₂ T₃ S₁ S₂ S₃)) = .some ⟨_, pure λ ((a, b, c) : T₁ × (T₂ × T₃)) => ((a, b), c)⟩ := by stop
  dsimp [environmentRhs, rhs]
  have : (("join " ++ S₁ ++ " (" ++ S₂ ++ " × " ++ S₃ ++ ")") == s!"pure ({S₁}×({S₂}×{S₃})) (({S₁}×{S₂})×{S₃})") = false := by sorry
  rw [Batteries.AssocList.find?.eq_2]; rw [this]; dsimp
  have : (s!"pure ({S₁}×({S₂}×{S₃})) (({S₁}×{S₂})×{S₃})" == s!"pure ({S₁}×({S₂}×{S₃})) (({S₁}×{S₂})×{S₃})") = true := by simp
  rw [Batteries.AssocList.find?.eq_2]; rw [this]

variable (T₁ T₂ T₃) in
def_module lhsModuleType : Type :=
  [T| (rewriteLhsRhs S₁ S₂ S₃).input_expr, (@environmentLhs T₁ T₂ T₃ S₁ S₂ S₃) ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
  simp only [find?_join1_data, find?_join2_data]
  dsimp

variable (T₁ T₂ T₃) in
def_module lhsModule : StringModule (lhsModuleType T₁ T₂ T₃) :=
  [e| (rewriteLhsRhs S₁ S₂ S₃).input_expr, @environmentLhs T₁ T₂ T₃ S₁ S₂ S₃ ]

variable (T₁ T₂ T₃) in
def_module rhsModuleType : Type :=
  [T| (rewriteLhsRhs S₁ S₂ S₃).output_expr, @environmentRhs T₁ T₂ T₃ S₁ S₂ S₃ ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
  simp only [find?_pure_data2, find?_join2_data2, find?_join2_data, find?_join1_data, find?_join1_data2]
  dsimp

variable (T₁ T₂ T₃) in
def_module rhsModule : StringModule (rhsModuleType T₁ T₂ T₃) :=
  [e| (rewriteLhsRhs S₁ S₂ S₃).output_expr, @environmentRhs T₁ T₂ T₃ S₁ S₂ S₃ ]

instance : MatchInterface (rhsModule T₁ T₂ T₃) (lhsModule T₁ T₂ T₃) := by
  dsimp [rhsModule, lhsModule]
  solve_match_interface

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

---------------------------------------------------------------------------------------------------
---
---------------------------------------------------------------------------------------------------

inductive at_least_single_internal: lhsModuleType T₁ T₂ T₃ -> Prop where
| mk: ∀ v q₁ q₂ q₃ q₄, at_least_single_internal ⟨⟨v :: q₃, q₄⟩, ⟨q₁, q₂⟩⟩

---------------------------------------------------------------------------------------------------
------------------------------------------- FLUSHABILITY ------------------------------------------
---------------------------------------------------------------------------------------------------

inductive partially_flushed: lhsModuleType T₁ T₂ T₃ -> Prop where
| lhs: ∀ lower arb, partially_flushed ⟨lower, [], arb⟩
| rhs: ∀ lower arb, partially_flushed ⟨lower, arb, []⟩

theorem pf_is_partially_flushed:
  ∀ s, pf (lhsModule T₁ T₂ T₃) s → partially_flushed s :=
by
  intro ⟨s1, s2, s3⟩ hr; dsimp [lhsModuleType, lhsModule] at *
  specialize hr ?r (by simp; rfl)
  cases s2 <;> cases s3 <;> try constructor
  exfalso
  apply hr ⟨⟨_, _⟩, ⟨_, _⟩⟩
  dsimp
  iterate 6 (apply Exists.intro _)
  and_intros <;> rfl

theorem partially_flushed_is_pf:
  ∀ s, partially_flushed s → pf (lhsModule T₁ T₂ T₃) s :=
by
  intro s h
  cases h
  all_goals
    unfold pf
    intros rule hᵣ _ h
    simp [lhsModule] at hᵣ <;> subst hᵣ
    simp at h

---------------------------------------------------------------------------------------------------
-----
---------------------------------------------------------------------------------------------------

instance {ident: InternalPort String} [MatchInterface (rhsModule T₁ T₂ T₃) (lhsModule T₁ T₂ T₃)]: Coe ((rhsModule T₁ T₂ T₃).inputs.getIO ident).fst ((lhsModule T₁ T₂ T₃).inputs.getIO ident).fst where
  coe := by
    intro h
    rename_i mi
    simpa [<- mi.input_types]

instance {ident: InternalPort String} [MatchInterface (rhsModule T₁ T₂ T₃) (lhsModule T₁ T₂ T₃)]: Coe ((rhsModule T₁ T₂ T₃).outputs.getIO ident).fst ((lhsModule T₁ T₂ T₃).outputs.getIO ident).fst where
  coe := by
    intro h
    rename_i mi
    simpa [<- mi.output_types]

---------------------------------------------------------------------------------------------------
----------- BASE RELATION BETWEEN (rhsModuleType T₁ T₂ T₃) and (lhsModuleType T₁ T₂ T₃) -----------
---------------------------------------------------------------------------------------------------

def ψ (rhs : rhsModuleType T₁ T₂ T₃) (lhs : lhsModuleType T₁ T₂ T₃) : Prop :=
  let ⟨⟨j2l, j2r⟩, ⟨j1l, j1r⟩⟩ := lhs
  let ⟨⟨j2l', j2r'⟩, ⟨⟨j1l', j1r'⟩, p⟩⟩ := rhs
  (j2l.map Prod.fst ++ j1l = p.map (Prod.fst ∘ Prod.fst) ++ j2l') ∧
  (j2l.map Prod.snd ++ j1r = p.map ((Prod.snd ∘ Prod.fst)) ++ j2r'.map Prod.fst ++ j1l') ∧
  (j2r = p.map Prod.snd ++ j2r'.map Prod.snd ++ j1r')

theorem ψ_holds_over_internals_spec:
  ∀ i s s', ψ i s → existSR (lhsModule T₁ T₂ T₃).internals s s' → ψ i s' :=
by
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

theorem ψ_holds_over_internals_impl:
  ∀ i i' s, ψ i s → existSR (rhsModule T₁ T₂ T₃).internals i i' → ψ i' s :=
by
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

theorem ψ_holds_over_internals: ∀ i i' s s',
  ψ i s → existSR (rhsModule T₁ T₂ T₃).internals i i' → existSR (lhsModule T₁ T₂ T₃).internals s s' → ψ i' s' :=
by
  intros i i' s s' _ _ _
  have: ψ i s' := by
    apply ψ_holds_over_internals_spec <;> assumption
  apply ψ_holds_over_internals_impl <;> assumption

theorem inputs_preserves_ψ: ∀ ident i₁ i₂ v s₁ s₂,
  ψ i₁ s₁
  → ((rhsModule T₁ T₂ T₃).inputs.getIO ident).snd i₁ ↑v i₂
  → ((lhsModule T₁ T₂ T₃).inputs.getIO ident).snd s₁ ↑v s₂
  → ψ i₂ s₂ :=
by
  intro ident ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ v ⟨⟨_, _⟩, ⟨_, _⟩⟩ ⟨⟨_, _⟩, ⟨_, _⟩⟩  h₁ h₂ h₃
  by_cases HContains: (rhsModule T₁ T₂ T₃).inputs.contains ident
  . simp [rhsModule] at HContains
    rcases HContains with h | h | h <;> subst h
    . --
      unfold lhsModule at h₃
      rw [PortMap.rw_rule_execution] at h₃
      simp at h₃
      obtain ⟨⟨_, _⟩, _, _⟩ := h₃
      --
      unfold rhsModule at h₂
      rw [PortMap.rw_rule_execution] at h₂
      simp at h₂
      obtain ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ := h₂
      --
      obtain ⟨_, _, _⟩ := h₁
      --
      subst_vars
      --
      dsimp [ψ]
      and_intros
      . rw [<- List.append_assoc, <- List.append_assoc]
        congr
      . assumption
      . rfl
    . --
      unfold lhsModule at h₃
      rw [PortMap.rw_rule_execution] at h₃
      simp at h₃
      obtain ⟨⟨_, _⟩, _, _⟩ := h₃
      --
      --
      unfold rhsModule at h₂
      rw [PortMap.rw_rule_execution] at h₂
      simp at h₂
      obtain ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩, _⟩ := h₂
      --
      obtain ⟨_, _, _⟩ := h₁
      subst_vars
      dsimp [ψ]
      and_intros
      . assumption
      . rw [<- List.append_assoc, <- List.append_assoc]
        congr
      . rfl
    . --
      unfold lhsModule at h₃
      rw [PortMap.rw_rule_execution] at h₃
      simp at h₃
      obtain ⟨⟨_, _⟩, _, _⟩ := h₃
      --
      --
      unfold rhsModule at h₂
      rw [PortMap.rw_rule_execution] at h₂
      simp at h₂
      obtain ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩, _⟩ := h₂
      --
      obtain ⟨_, _, _⟩ := h₁
      --
      subst_vars
      --
      dsimp [ψ]
      and_intros
      . assumption
      . assumption
      . simp
  . exfalso; exact (PortMap.getIO_not_contained_false h₂ HContains)

theorem outputs_preserves_ψ: ∀ ident i₁ i₂ v s₁ s₂,
  ψ i₁ s₁
  → ((rhsModule T₁ T₂ T₃).outputs.getIO ident).snd i₁ ↑v i₂
  → ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₁ ↑v s₂
  → ψ i₂ s₂ :=
by
  intro ident ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ v ⟨⟨_, _⟩, ⟨_, _⟩⟩ ⟨⟨_, _⟩, ⟨_, _⟩⟩ h₁ h₂ h₃
  by_cases HContains: ((rhsModule T₁ T₂ T₃).outputs.contains ident)
  . simp [rhsModule] at HContains; subst HContains
    unfold rhsModule at h₂
    rw [PortMap.rw_rule_execution] at h₂; simp at h₂
    repeat
      cases ‹_ ∧ _›
    simp at *
    cases ‹_ ∧ _›
    subst_vars

    dsimp [ψ]
    and_intros
    . simp at *; assumption
    . simp at *; assumption
    . simp at *; assumption
  . exfalso; exact (PortMap.getIO_not_contained_false h₃ HContains)

theorem f₆: ∀ ident i₁ i₂ v s₁,
  ψ i₁ s₁
  → pf ((lhsModule T₁ T₂ T₃)) s₁
  → ((rhsModule T₁ T₂ T₃).outputs.getIO ident).snd i₁ v i₂
  → at_least_single_internal s₁ :=
by
  intro ident ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ v ⟨⟨_, _⟩, ⟨_, _⟩⟩ h₁ h₂ h₃
  by_cases HContains: (rhsModule T₁ T₂ T₃).outputs.contains ident
  .
    simp [rhsModule] at HContains <;> subst HContains
    --
    unfold rhsModule at h₃
    rw [PortMap.rw_rule_execution] at h₃
    simp at h₃
    obtain ⟨⟨_, _, _⟩, _, _⟩ := h₃
    obtain ⟨_, _, _⟩ := h₁
    subst_vars
    --
    apply pf_is_partially_flushed at h₂
    cases h₂
    . rename_i h₁ h₂
      simp at h₁ h₂
      sorry -- TODO: Reasoning about the length again?
    . rename_i h₁ h₂
      simp at h₁ h₂
      sorry -- TODO: Reasoning about the length again?
  . exfalso; exact (PortMap.getIO_not_contained_false h₃ HContains)

-- move to have a reasoning about atleast one in internal
-- we case only on once over queues that are in the top queue
theorem f₅: ∀ ident i₁ i₂ v s₁,
  ψ i₁ s₁
  → at_least_single_internal s₁
  → ((rhsModule T₁ T₂ T₃).outputs.getIO ident).snd i₁ ↑v i₂
  → ∃ s₂, ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₁ ↑v s₂ :=
by
  intro ident ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ v s₁ h₁ h₂ h₃
  by_cases HContains: (rhsModule T₁ T₂ T₃).outputs.contains ident
  . simp [rhsModule] at HContains <;> subst HContains
    --
    unfold rhsModule at h₃
    rw [PortMap.rw_rule_execution] at h₃
    simp at h₃
    obtain ⟨⟨_, _, _⟩, _, _⟩ := h₃
    subst_vars
    --
    cases h₂
    obtain ⟨_, _, _⟩ := h₁
    apply Exists.intro ⟨⟨_, _⟩, ⟨_, _⟩⟩
    unfold lhsModule
    rw [PortMap.rw_rule_execution]
    simp
    and_intros
    . rw [List.map_cons, List.map_cons] at *
      simp at *
      iterate 2
        cases ‹_ ∧ _›
      apply Prod.ext <;> assumption
    . rfl
    . rw [List.map_cons] at *; assumption
    . rfl
    . rfl
  . exfalso; exact (PortMap.getIO_not_contained_false h₃ HContains)

---------------------------------------------------------------------------------------------------
-----------------
---------------------------------------------------------------------------------------------------

theorem lhs_can_always_flush:
  ∀ s, ∃ s', existSR (lhsModule T₁ T₂ T₃).internals s s' ∧ pf (lhsModule T₁ T₂ T₃) s' :=
by
  intro ⟨⟨l1, l2⟩, ⟨l3, l4⟩⟩
  induction l3 generalizing l1 l2 l4 with
  | nil =>
    apply Exists.intro
    and_intros
    . apply existSR_reflexive
    . apply partially_flushed_is_pf <;>
      constructor
  | cons x xs ih =>
    cases l4
    . apply Exists.intro
      and_intros
      . apply existSR_reflexive
      . apply partially_flushed_is_pf <;> constructor
    . rename_i head tail
      specialize ih (l1 ++ [(x, head)]) l2 tail
      obtain ⟨ ⟨⟨_, _⟩, ⟨_, _⟩⟩, _, _⟩ := ih
      apply Exists.intro ⟨ ⟨ _, _ ⟩, _, _ ⟩
      and_intros
      . apply existSR.step _ ⟨ ⟨ _, _ ⟩, _, _ ⟩ _
        . unfold lhsModule; simp; rfl
        . repeat apply Exists.intro
          and_intros <;> rfl
        . assumption
      . assumption

theorem lhs_can_always_input:
  ∀ ident s₁ v,
  (lhsModule T₁ T₂ T₃).inputs.contains ident
  → ∃ s₂, ((lhsModule T₁ T₂ T₃).inputs.getIO ident).snd s₁ v s₂ :=
by
  intro ident ⟨⟨q₁, q₂⟩, ⟨q₃, q₄⟩⟩ v h
  simp [lhsModule] at h
  rcases h with h | h | h <;> subst h
  . have: ((lhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_2" }).fst = T₃ := by
      simp [lhsModule, PortMap.getIO]
    use ⟨⟨q₁, q₂ ++ [(this.mp v)]⟩, ⟨q₃, q₄⟩⟩
    dsimp [lhsModule]
    rw [PortMap.rw_rule_execution]
    simp
  . have: ((lhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_0" }).fst = T₁ := by
      simp [lhsModule, PortMap.getIO]
    use ⟨⟨q₁, q₂⟩, ⟨q₃ ++ [(this.mp v)], q₄⟩⟩
    dsimp [lhsModule]
    rw [PortMap.rw_rule_execution]
    simp
  . have: ((lhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_1" }).fst = T₂ := by
      simp [lhsModule, PortMap.getIO]
    use ⟨⟨q₁, q₂⟩, ⟨q₃, q₄ ++ [(this.mp v)]⟩⟩
    dsimp [lhsModule]
    rw [PortMap.rw_rule_execution]
    simp

theorem flhs_can_always_input:
  ∀ ident s₁ v,
  (lhsModule T₁ T₂ T₃).inputs.contains ident
  → ∃ s₂, ((flushed (lhsModule T₁ T₂ T₃)).inputs.getIO ident).snd s₁ v s₂ :=
by
  intro ident s₁ v _
  have: ∃ s₂, ((lhsModule T₁ T₂ T₃).inputs.getIO ident).snd s₁ ((flushed_preserves_input_over_getIO (lhsModule T₁ T₂ T₃) ident).mp v) s₂ := by
    apply lhs_can_always_input <;> assumption
  obtain ⟨s₃, h⟩ := this
  have: ∃ s', existSR (lhsModule T₁ T₂ T₃).internals s₃ s' ∧ pf (lhsModule T₁ T₂ T₃) s' := by
    apply lhs_can_always_flush
  have ⟨s₄, _, _⟩ := this
  use s₄
  have: (flushed (lhsModule T₁ T₂ T₃)).inputs.getIO ident = rflushed (lhsModule T₁ T₂ T₃) ((lhsModule T₁ T₂ T₃).inputs.getIO ident) := by
    apply flushed_inputs_are_rflushed
    apply PortMap.rule_contains at h
    assumption
  rw [sigma_rw this]
  dsimp [rflushed]
  use s₃
  and_intros <;> assumption

---------------------------------------------------------------------------------------------------
----------
---------------------------------------------------------------------------------------------------

theorem lengthify {T₁: Type _} (a b: List T₁): a = b → a.length = b.length := by
  intro heq; rw [heq]

theorem takify {T₁: Type _} (l: ℕ) (l₁ l₂: List T₁): l₁ = l₂ -> List.take l l₁ = List.take l l₂ := by
  intro heq; rw [heq]

theorem dropify {T₁: Type _} (l: ℕ) (l₁ l₂: List T₁): l₁ = l₂ -> List.drop l l₁ = List.drop l l₂ := by
  intro heq; rw [heq]

theorem product_is_list_zip {T₁ T₂: Type _} (x: List (T₁ × T₂)):
  x = List.zip (List.map Prod.fst x) (List.map Prod.snd x) :=
by
  induction x with
  | nil => simp
  | cons head tail ih =>
    simp only [List.map_cons, List.zip_cons_cons, <- ih]

theorem append_iff {α} {a b c d : List α}:
  a.length = c.length → (a ++ b = c ++ d ↔ a = c ∧ b = d) :=
by
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

theorem bla {α : Type _} {a c : α} (b : List α) :
  a ∈ b → c ∈ b → b.length = 1 → a = c :=
by
  intro ha hc hl
  cases b with
  | nil => exfalso; rw [List.length_nil] at hl; contradiction
  | cons x xs => cases xs with
    | nil =>
      simp at *; subst_vars; rfl
    | cons x' xs' =>
      repeat rw [List.length_cons] at hl
      rw [Nat.add_eq_right] at hl
      rw [Nat.add_eq_zero] at hl
      cases ‹ _ ∧ _ ›
      contradiction

---------------------------------------------------------------------------------------------------
--------------------------------------- LHS IS DETERMINISTIC --------------------------------------
---------------------------------------------------------------------------------------------------

theorem input_rules_deterministic: ∀ ident s₁ v s₂ s₃,
  ((lhsModule T₁ T₂ T₃).inputs.getIO ident).snd s₁ v s₂
  → ((lhsModule T₁ T₂ T₃).inputs.getIO ident).snd s₁ v s₃
  → s₂ = s₃ :=
by
  intro ident ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ _ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ h₁ h₂
  by_cases HContains: ((lhsModule T₁ T₂ T₃).inputs.contains ident)
  . simp [lhsModule] at HContains
    rcases HContains with h | h | h <;> subst h
    all_goals
      dsimp [lhsModule] at h₁ h₂
      rw [PortMap.rw_rule_execution] at h₁ h₂
      dsimp at h₁ h₂
      repeat
        cases ‹_ ∧ _›
        try simp at *
        try subst_vars
      rfl
  . exfalso; exact (PortMap.getIO_not_contained_false (by assumption) HContains)

theorem internal_rules_deterministic:
  ∀ rule ∈ (lhsModule T₁ T₂ T₃).internals , ∀ s₁ s₂ s₃, rule s₁ s₂ → rule s₁ s₃ → s₂ = s₃ :=
by
  intro _ _ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ h₁ h₂
  simp [lhsModule] at *
  subst_vars
  dsimp at h₁ h₂
  obtain ⟨_, _, _, _, _, _, _⟩ := h₁
  obtain ⟨_, _, _, _, _, _, _⟩ := h₂
  repeat
    cases ‹_ ∧ _›
    try simp at *
    try subst_vars
  rfl

theorem output_rules_deterministic: ∀ ident s₁ v s₂ s₃,
  ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₁ v s₂
  → ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₁ v s₃
  → s₂ = s₃ :=
by
  intro ident ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ _ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ h₁ h₂
  by_cases HContains: ((lhsModule T₁ T₂ T₃).outputs.contains ident)
  . simp [lhsModule] at HContains; subst HContains
    dsimp [lhsModule] at h₁ h₂
    rw [PortMap.rw_rule_execution] at h₁ h₂
    dsimp at h₁ h₂
    repeat
      cases ‹_ ∧ _›
      try simp at *
      try subst_vars
    rfl
  . exfalso; exact (PortMap.getIO_not_contained_false (by assumption) HContains)

open Module.Determinism in
instance: Deterministic (lhsModule T₁ T₂ T₃) :=
  {
    input_deterministic    := input_rules_deterministic
    internal_deterministic := internal_rules_deterministic
    output_deterministic   := output_rules_deterministic
  }

---------------------------------------------------------------------------------------------------
--------------------------------------- LHS SPECIFIC LEMMAS ---------------------------------------
---------------------------------------------------------------------------------------------------

theorem hamza₂: ∀ rule ∈ (lhsModule T₁ T₂ T₃).internals, ∀ ident s₁ v s₂ s₃,
  ((lhsModule T₁ T₂ T₃).inputs.getIO ident).snd s₁ v s₂
  → ∃ s₄, ((lhsModule T₁ T₂ T₃).inputs.getIO ident).snd s₃ v s₄ :=
by
  intro rule _ ident _ _ _ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ _
  by_cases HContains: ((lhsModule T₁ T₂ T₃).inputs.contains ident)
  . -- TODO: Extract it as it's own theorem
    simp [lhsModule] at HContains
    rcases HContains with h | h | h <;> subst h
    all_goals
      apply Exists.intro ⟨⟨_ , _⟩, ⟨_ , _⟩⟩
      dsimp [lhsModule]
      rw [PortMap.rw_rule_execution]
      simp <;> and_intros <;> rfl
  . exfalso; exact (PortMap.getIO_not_contained_false (by assumption) HContains)

theorem hamza: ∀ ident s₁ v s₂ s₃,
  existSR (lhsModule T₁ T₂ T₃).internals s₁ s₃
  → ((lhsModule T₁ T₂ T₃).inputs.getIO ident).snd s₁ v s₂
  → ∃ s₄, ((lhsModule T₁ T₂ T₃).inputs.getIO ident).snd s₃ v s₄ :=
by
  intros ident s₁ v s₂ s₃ h _
  induction h generalizing s₂ with
  | done => use s₂
  | step init mid final rule _ _ _ ih =>
    have: (∃ s₄, ((lhsModule T₁ T₂ T₃).inputs.getIO ident).snd mid v s₄) := by
      apply hamza₂ <;> assumption
    obtain ⟨s, h⟩ := this
    specialize ih s
    apply ih
    assumption

theorem b': ∀ rule ∈ (lhsModule T₁ T₂ T₃).internals, ∀ ident s₁ v s₂ s₃,
  ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₁ v s₂
  → rule s₁ s₃
  → ∃ s₄, ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₃ v s₄ :=
by
  intro rule hᵣ ident ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ v ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ h₁ h₂
  by_cases HContains: ((lhsModule T₁ T₂ T₃).outputs.contains ident)
  . simp [lhsModule] at HContains
    simp [lhsModule] at hᵣ
    unfold lhsModule at h₁
    rw [PortMap.rw_rule_execution] at h₁
    subst_vars
    dsimp at *
    obtain ⟨_, _, _, _, _, _, ⟨⟨_ , _⟩ , _⟩, ⟨_ , _⟩, _⟩ := h₂
    simp at *; subst_vars
    repeat cases ‹_ ∧ _›
    subst_vars; simp
    -- extract this as it's own lemma
    apply Exists.intro ⟨⟨_ , _⟩, ⟨_ , _⟩⟩
    dsimp [lhsModule]
    rw [PortMap.rw_rule_execution]
    dsimp <;> and_intros <;> rfl
  . exfalso; exact (PortMap.getIO_not_contained_false h₁ HContains)

theorem b'': ∀ ident s₁ v s₂ s₃,
  existSR (lhsModule T₁ T₂ T₃).internals s₁ s₃
  → ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₁ v s₂
  → ∃ s₄, ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₃ v s₄ :=
by
  intros ident s₁ v s₂ s₃ h _
  induction h generalizing s₂ with
  | done => use s₂
  | step init mid final rule _ _ _ ih =>
    have: (∃ s₄, ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd mid v s₄) := by
      apply b' <;> assumption
    obtain ⟨s, h⟩ := this
    specialize ih s
    apply ih
    assumption

theorem b'₄: ∀ rule ∈ (lhsModule T₁ T₂ T₃).internals, ∀ ident s₁ v s₂ s₃ s₄,
  ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₁ v s₂
  → rule s₁ s₃
  → rule s₂ s₄
  → ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₃ v s₄ :=
by
  intro rule h₁ ident ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ _ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ h₂ h₃ h₄
  by_cases HContains: ((lhsModule T₁ T₂ T₃).outputs.contains ident)
  . -- process and unfold the fact that use the internal rule
    simp [lhsModule] at h₁; subst h₁; dsimp at h₃ h₄
    -- process the fact we use the output rule
    simp [lhsModule] at HContains; subst HContains
    dsimp [lhsModule] at h₂
    rw [PortMap.rw_rule_execution] at h₂
    dsimp at h₂
    dsimp [lhsModule]
    rw [PortMap.rw_rule_execution]
    dsimp
    obtain ⟨_, _, _, _, _, _, _⟩ := h₃
    obtain ⟨_, _, _, _, _, _, _⟩ := h₄
    repeat
      cases ‹_ ∧ _›
      try simp at *
      try subst_vars
    and_intros <;> rfl
  . exfalso; exact (PortMap.getIO_not_contained_false (by assumption) HContains)

theorem b'₃: ∀ rule ∈ (lhsModule T₁ T₂ T₃).internals, ∀ ident s₁ v s₂ s₃,
  ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₁ v s₂
  → rule s₁ s₃
  → ∃ s₄, rule s₂ s₄ :=
by
  intro rule h₁ ident ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ _ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ h₃ h₂
  by_cases HContains: ((lhsModule T₁ T₂ T₃).outputs.contains ident)
  . simp [lhsModule] at HContains; subst HContains
    unfold lhsModule at h₃
    rw [PortMap.rw_rule_execution] at h₃
    dsimp at h₃
    simp [lhsModule] at h₁; subst h₁
    obtain ⟨_, _, _, _, _, _, ⟨⟨_ , _⟩ , _⟩, ⟨_ , _⟩, _⟩ := h₂
    simp at *; subst_vars
    repeat cases ‹ _ ∧ _ ›
    subst_vars; simp
    apply Exists.intro ⟨⟨_ , _⟩, ⟨_ , _⟩⟩; and_intros <;> rfl
  . exfalso; exact (PortMap.getIO_not_contained_false (by assumption) HContains)

theorem b₃: ∀ ident s₁ v s₂ s₃ s₄,
  existSR (lhsModule T₁ T₂ T₃).internals s₁ s₃
  → ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₁ v s₂
  → ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₃ v s₄
  → existSR (lhsModule T₁ T₂ T₃).internals s₂ s₄:=
by
  intros ident s₁ v s₂ s₃ s₄ h _ _
  induction h generalizing s₂ with
  | done =>
    have: s₂ = s₄ := by
      apply output_rules_deterministic <;> assumption
    subst this
    apply existSR_reflexive
  | step init mid _ rule _ _ _ ih =>
    have: (∃ mid', rule s₂ mid' ∧ existSR (lhsModule T₁ T₂ T₃).internals mid' s₄) := by
      have: (∃ m, rule s₂ m) := by
        apply b'₃ <;> assumption
      obtain ⟨m, _⟩ := this
      use m
      and_intros
      . assumption
      . apply ih
        . apply b'₄ _ _ _ init _ s₂ <;> assumption
        . assumption
    obtain ⟨mid', _, _⟩ := this
    apply existSR_transitive _ _ mid'
    . apply existSR_single_step <;> and_intros <;> assumption
    . assumption

theorem b'₅: ∀ rule ∈ (lhsModule T₁ T₂ T₃).internals, ∀ ident s₁ v s₂ s₃ s₄,
  ((lhsModule T₁ T₂ T₃).inputs.getIO ident).snd s₁ v s₂
  → ((lhsModule T₁ T₂ T₃).inputs.getIO ident).snd s₃ v s₄
  → rule s₁ s₃
  → rule s₂ s₄ :=
by
  intro rule hᵣ ident ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ _ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ hᵢ hᵢ' hᵣ'
  by_cases HContains: ((lhsModule T₁ T₂ T₃).inputs.contains ident)
  . -- extract the names of the ports
    simp [lhsModule] at HContains
    -- work on the internal rules
    simp [lhsModule] at hᵣ <;> subst hᵣ
    obtain ⟨_, _, _, _, _, _, ⟨⟨_ , _⟩ , _⟩, ⟨_ , _⟩, _⟩ := hᵣ'
    simp at * <;> (repeat cases ‹_ ∧ _›) <;> subst_vars
    -- work on each input rule
    rcases HContains with h | h | h <;> subst h
    all_goals
      dsimp [lhsModule] at hᵢ hᵢ'
      rw [PortMap.rw_rule_execution] at hᵢ hᵢ'
      dsimp at hᵢ hᵢ'
      obtain ⟨⟨_ , _⟩, _, _⟩ := hᵢ
      obtain ⟨⟨_ , _⟩, _, _⟩ := hᵢ'
      subst_vars
      simp
  . exfalso; exact (PortMap.getIO_not_contained_false (by assumption) HContains)

---------------------------------------------------------------------------------------------------
-----------
---------------------------------------------------------------------------------------------------

theorem bll'₂ {Ident S: Type _} [DecidableEq Ident] (mod: Module Ident S): ∀ ident s₁ v s₂ s₃,
  (mod.inputs.getIO ident).snd s₁ v s₂
  → existSR (mod.internals) s₂ s₃
  → pf mod s₃
  → ((flushed mod).inputs.getIO ident).snd s₁ ((flushed_preserves_input_over_getIO' mod ident).mp v) s₃ :=
by
  intro ident s₁ v s₂ s₃ h₁ h₂ h₃
  by_cases HContains: mod.inputs.contains ident
  . have: (flushed mod).inputs.getIO ident = rflushed mod (mod.inputs.getIO ident) := by
      apply flushed_inputs_are_rflushed <;> assumption
    rw [sigma_rw this]
    dsimp [rflushed]
    use s₂
    and_intros <;> simpa
  . exfalso; exact (PortMap.getIO_not_contained_false (by assumption) HContains)

theorem abc: ∀ ident s₁ v s₂,
  ((lhsModule T₁ T₂ T₃).inputs.getIO ident).snd s₁ v s₂
  → ∃ s₃, ((flushed (lhsModule T₁ T₂ T₃)).inputs.getIO ident).snd s₁ ((flushed_preserves_input_over_getIO' (lhsModule T₁ T₂ T₃) ident).mp v) s₃ :=
by
  intros ident _ _ s₂ _
  have: ∃ s₃, existSR (lhsModule T₁ T₂ T₃).internals s₂ s₃ ∧ pf (lhsModule T₁ T₂ T₃) s₃ := by
      apply lhs_can_always_flush s₂
  obtain ⟨s₃, _, h⟩ := this
  use s₃
  apply bll'₂ <;> assumption

theorem bll'₃: ∀ ident s v s',
  ((lhsModule T₁ T₂ T₃).inputs.getIO ident).snd s v s'
  -> ∃ s'', ((flushed (lhsModule T₁ T₂ T₃)).inputs.getIO ident).snd s ((flushed_preserves_input_over_getIO' (lhsModule T₁ T₂ T₃) ident).mp v) s'' ∧ existSR ((lhsModule T₁ T₂ T₃).internals) s' s'' ∧ pf (lhsModule T₁ T₂ T₃) s'' :=
by
  intros ident s v _ _
  have: ∃ s'', ((flushed (lhsModule T₁ T₂ T₃)).inputs.getIO ident).snd s ((flushed_preserves_input_over_getIO' (lhsModule T₁ T₂ T₃) ident).mp v) s'' := by
    apply abc <;> assumption
  obtain ⟨s₁, h⟩ := this
  use s₁
  and_intros <;> try assumption
  . apply flushed_reachable_from_nonflushed
    all_goals
      simp at * -- TODO: Can I get rid of this simp?
      assumption
  . apply flushed_modules_has_flushed_states <;> assumption

---------------------------------------------------------------------------------------------------
-----
---------------------------------------------------------------------------------------------------

-- "if we pop an output from a flushed state, the resulting state is also flushed"
theorem b₂: ∀ ident s₁ v s₂,
  pf (lhsModule T₁ T₂ T₃) s₁
  → ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₁ v s₂
  →  pf (lhsModule T₁ T₂ T₃) s₂ :=
by
  intro ident ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ _ ⟨⟨_ , _⟩, ⟨_ , _⟩⟩ hpf h₁
  apply pf_is_partially_flushed at hpf
  apply partially_flushed_is_pf
  by_cases HContains: ((lhsModule T₁ T₂ T₃).outputs.contains ident)
  . simp [lhsModule] at HContains <;> subst HContains
    dsimp [lhsModule] at h₁
    rw [PortMap.rw_rule_execution] at h₁
    repeat
      cases ‹_ ∧ _›; simp at *
    subst_vars
    cases hpf <;> constructor
  . exfalso; exact (PortMap.getIO_not_contained_false (by assumption) HContains)

---------------------------------------------------------------------------------------------------
-------------------------- NON-FLUSHED, NON-INDUCTIVE ψ PROOF (BASELINE) --------------------------
---------------------------------------------------------------------------------------------------

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

theorem refines₀: rhsModule T₁ T₂ T₃ p⊑_{φ} lhsModule T₁ T₂ T₃ := by
  unfold Module.prefines_φ
  intro init_i init_s Hφ
  apply Module.pcomp_refines.mk
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
        have_hole heq : ((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_0" }).fst = _ := by dsimp [reducePortMapgetIO]
        -- We construct the almost_mid_s manually
        use ⟨⟨sj2l, sj2r⟩, ⟨sj1l ++ [heq.mp s], sj1r⟩⟩
        apply And.intro
        . -- verify that the rule holds
          rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]
          simp
        . -- verify that the invariant holds when we flush the system
          obtain ⟨s', ⟨_, _⟩⟩ := lhs_can_always_flush ⟨⟨sj2l, sj2r⟩, sj1l ++ [heq.mp s], sj1r⟩ -- We flush the system to reach s'
          use s'
          apply And.intro
          . assumption
          . unfold φ at *
            apply And.intro
            . apply ψ_holds_over_internals_spec _ (⟨sj2l, sj2r⟩, sj1l ++ [heq.mp s], sj1r) s'
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
            . apply pf_is_partially_flushed <;> assumption
      . obtain ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩, _⟩ := a
        subst_vars
        reduce at s
        use ⟨⟨sj2l, sj2r⟩, ⟨sj1l, sj1r ++ [s]⟩⟩
        apply And.intro
        . rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; simp
        . obtain ⟨s', ⟨_, _⟩⟩ := lhs_can_always_flush ⟨⟨sj2l, sj2r⟩, sj1l, sj1r ++ [s]⟩
          use s'
          apply And.intro
          . assumption
          . unfold φ at *
            apply And.intro
            . apply ψ_holds_over_internals_spec _ (⟨sj2l, sj2r⟩, sj1l, sj1r ++ [s]) s'
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
            . apply pf_is_partially_flushed <;> assumption
      . obtain ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩, _⟩ := a
        subst_vars
        reduce at s
        use ⟨⟨sj2l, sj2r ++ [s]⟩, ⟨sj1l, sj1r⟩⟩
        apply And.intro
        . rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; simp
        . obtain ⟨s', ⟨_, _⟩⟩ := lhs_can_always_flush ⟨⟨sj2l, sj2r ++ [s]⟩, sj1l, sj1r⟩
          use s'
          apply And.intro
          . assumption
          . unfold φ at *
            apply And.intro
            . apply ψ_holds_over_internals_spec _ (⟨sj2l, sj2r  ++ [s]⟩, sj1l, sj1r) s'
              . obtain ⟨Hψ, _⟩ := Hφ
                unfold ψ at *; simp at *
                obtain ⟨_, _, _⟩ := Hψ
                subst_vars
                and_intros
                . assumption
                . assumption
                . simp only [<- List.append_assoc, List.append_left_inj] at *
              . assumption
            . apply pf_is_partially_flushed <;> assumption
    . exfalso; exact (PortMap.getIO_not_contained_false a HContains)
  -- output rules
  . intro ident i v hrule
    by_cases HContains: ((rhsModule T₁ T₂ T₃).outputs.contains ident)
    ·
      obtain ⟨⟨sj2l, sj2r⟩, ⟨sj1l, sj1r⟩⟩ := init_s
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
      . apply ψ_holds_over_internals_impl init_i
        . assumption
        . apply existSR_single_step' <;> assumption
      . assumption

---------------------------------------------------------------------------------------------------
------------------- FLUSHED, INDUCTIVE, OVER LHS PROOF THAT (LHS ⊑ FLUSHED LHS) -------------------
---------------------------------------------------------------------------------------------------

def φ₂ {Ident S: Type _} (mod: Module Ident S)(lhs : S) (rhs : S) : Prop :=
  existSR mod.internals lhs rhs ∧ pf mod rhs

theorem refines₂:
  lhsModule T₁ T₂ T₃ p⊑_{φ₂ (lhsModule T₁ T₂ T₃)} flushed (lhsModule T₁ T₂ T₃) :=
by
  unfold Module.prefines_φ
  intro init_i init_s ⟨Hφ, hpf⟩
  apply Module.pcomp_refines.mk <;> unfold φ₂ at *
  -- input rules
  . intro ident mid_i v h
    induction Hφ generalizing mid_i with
    | done =>
      apply bll'₃ at h
      obtain ⟨s, _, _, _⟩ := h
      use s, s
      and_intros <;> try assumption
      apply existSR_reflexive
    | step init mid _ rule _ _ _ ih =>
      specialize ih (by assumption)
      have: ∃ s, ((lhsModule T₁ T₂ T₃).inputs.getIO ident).snd mid v s := by
        apply hamza <;> try assumption
        apply existSR_single_step <;> and_intros <;> assumption
      obtain ⟨s, _⟩ := this
      specialize ih s (by assumption)
      obtain ⟨s₁, s₂, _, _, _, _⟩ := ih
      use s₁, s₂
      and_intros <;> try assumption
      rename_i a _ _
      dsimp [flushed] at a
      apply existSR_norules at a; subst a
      have: rule mid_i s := by apply b'₅ <;> assumption
      apply (existSR_single_step' (lhsModule T₁ T₂ T₃).internals) at this <;> try assumption
      apply existSR_transitive (lhsModule T₁ T₂ T₃).internals _ s <;> assumption
  -- output rules
  . intro _ mid_i _ h
    dsimp [flushed] at *
    apply b'' at Hφ
    specialize Hφ h
    obtain ⟨mid_s, _⟩ := Hφ
    use mid_s
    and_intros <;> try assumption
    . apply b₃ <;> assumption
    . apply b₂ <;> assumption
  -- internal rules
  . intros rule mid_i HRuleInInternal _
    use init_s
    and_intros
    . apply existSR_reflexive
    . cases Hφ with
      | done =>
        unfold pf at hpf
        specialize hpf rule (by exact HRuleInInternal) mid_i
        contradiction
      | step _ mid _ rule' _ _ _ =>
          have: rule = rule' := by
            apply bla at HRuleInInternal
            specialize HRuleInInternal (by assumption) (by dsimp[lhsModule])
            assumption
          subst this
          have: mid_i = mid := by
            apply internal_rules_deterministic <;> assumption
          subst this <;> assumption
    . assumption

---------------------------------------------------------------------------------------------------
---------
---------------------------------------------------------------------------------------------------

inductive empty_internal: lhsModuleType T₁ T₂ T₃ -> Prop where
| mk: ∀ q₁ q₂ q₃, empty_internal ⟨⟨[], q₃⟩, ⟨q₁, q₂⟩⟩

inductive single_internal: lhsModuleType T₁ T₂ T₃ -> Prop where
| mk: ∀ v q₁ q₂ q₃, single_internal ⟨⟨[v], q₃⟩, ⟨q₁, q₂⟩⟩

theorem f': ∀ s₁ s₂, ∀ rule ∈ (lhsModule T₁ T₂ T₃).internals,
  empty_internal s₁
  → rule s₁ s₂
  → single_internal s₂ :=
by
  intro ⟨⟨_, _⟩,⟨_, _⟩⟩ ⟨⟨_, _⟩,⟨_, _⟩⟩ rule h₁ h₂ h₃
  simp [lhsModule] at h₁
  subst h₁

  cases h₂
  dsimp at h₃
  simp at h₃
  obtain ⟨_, _, _, _, _, _, _⟩ := h₃
  repeat
    cases ‹_ ∧ _›
  subst_vars
  rw [List.nil_append]
  constructor

theorem f₃: ∀ ident s₁ s₂ v,
  single_internal s₁
  → ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₁ v s₂
  → empty_internal s₂ :=
by
  intro ident ⟨⟨_, _⟩,⟨_, _⟩⟩ ⟨⟨_, _⟩,⟨_, _⟩⟩ _ h₁ h₂
  by_cases HContains: ((lhsModule T₁ T₂ T₃).outputs.contains ident)
  . -- fetch the single output port ident
    simp [lhsModule] at HContains; subst HContains
    unfold lhsModule at h₂
    rw [PortMap.rw_rule_execution] at h₂
    dsimp at h₂
    simp at h₂
    repeat
      cases ‹_ ∧ _›
    subst_vars
    cases h₁
    constructor
  . exfalso; exact (PortMap.getIO_not_contained_false (by assumption) HContains)

---------------------------------------------------------------------------------------------------
---------
---------------------------------------------------------------------------------------------------

def φ₃ (rhs : rhsModuleType T₁ T₂ T₃) (lhs : lhsModuleType T₁ T₂ T₃) :=
  ψ rhs lhs ∧ empty_internal lhs

theorem f₁: ∀ ident i₁ i₂ v s₁, ∀ rule ∈ (lhsModule T₁ T₂ T₃).internals,
  φ₃ i₁ s₁
  → ((rhsModule T₁ T₂ T₃).outputs.getIO ident).snd i₁ v i₂
  → ∃ s₂, rule s₁ s₂ :=
by
  intro ident ⟨⟨_, _⟩,⟨_, _⟩⟩ ⟨⟨_, _⟩,⟨_, _⟩⟩ v ⟨⟨_, _⟩,⟨_, _⟩⟩ rule h₁ h₂ h₃
  by_cases HContains: ((rhsModule T₁ T₂ T₃).outputs.contains ident)
  . -- Fetch the output rule
    simp [rhsModule] at HContains; subst HContains
    obtain ⟨hψ, h₂⟩ := h₂
    cases h₂
    dsimp [ψ] at hψ
    obtain ⟨_, _, _⟩ := hψ
    subst_vars
    -- work on h₃
    unfold rhsModule at h₃
    rw [PortMap.rw_rule_execution] at h₃
    simp at h₃
    repeat
      cases ‹_ ∧ _›
    subst_vars
    -- work on h₁
    simp [lhsModule] at h₁; subst h₁
    dsimp
    apply Exists.intro ⟨⟨_, _⟩,⟨_, _⟩⟩
    repeat
      apply Exists.intro
    simp
    and_intros <;> rfl
  . exfalso; exact (PortMap.getIO_not_contained_false (by assumption) HContains)

theorem f'': ∀ ident i₁ i₂ v s₁,
  ψ i₁ s₁
  → single_internal s₁
  → ((rhsModule T₁ T₂ T₃).outputs.getIO ident).snd i₁ ↑v i₂
  → ∃ s₂, ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd s₁ ↑v s₂ :=
by
  intro ident ⟨⟨_, _⟩,⟨_, _⟩⟩ ⟨⟨_, _⟩,⟨_, _⟩⟩ _ ⟨⟨_, _⟩,⟨_, _⟩⟩ h₁ h₂ h₃
  by_cases HContains: ((rhsModule T₁ T₂ T₃).outputs.contains ident)
  . simp [rhsModule] at HContains; subst HContains
    unfold rhsModule at h₃; rw [PortMap.rw_rule_execution] at h₃; simp at h₃
    cases h₂
    dsimp [ψ] at h₁
    repeat
      cases ‹_ ∧ _›
    subst_vars
    unfold lhsModule
    apply Exists.intro ⟨⟨_, _⟩,⟨_, _⟩⟩
    rw [PortMap.rw_rule_execution]; dsimp
    and_intros
    . simp at *
      iterate 2 cases ‹_ ∧ _›
      and_intros
      . apply Prod.ext <;> assumption
      . rfl
    . rfl
    . rfl
  . exfalso; exact (PortMap.getIO_not_contained_false (by assumption) HContains)

theorem refines₃: rhsModule T₁ T₂ T₃ ⊑_{φ₃} lhsModule T₁ T₂ T₃ := by
  unfold Module.refines_φ
  intro init_i init_s Hψ
  apply Module.comp_refines.mk
  -- input rules
  . intro ident i s a
    by_cases HContains: ((rhsModule T₁ T₂ T₃).inputs.contains ident)
    . obtain ⟨⟨sj2l, sj2r⟩, ⟨sj1l, sj1r⟩⟩ := init_s
      obtain ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ := init_i
      obtain ⟨⟨_, _⟩, ⟨_, _⟩, _⟩ := i

      unfold rhsModule at HContains; simp at HContains
      rcases HContains with h | h | h <;> subst_vars <;> simp
      . unfold rhsModule at a
        rw [PortMap.rw_rule_execution] at a
        dsimp at a
        obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := a
        subst_vars
        have_hole heq : ((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_0" }).fst = _ := by dsimp [reducePortMapgetIO]
        -- We construct the almost_mid_s manually
        use ⟨⟨sj2l, sj2r⟩, ⟨sj1l ++ [heq.mp s], sj1r⟩⟩
        apply And.intro
        . -- verify that the rule holds
          rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]
          simp -- TODO: Remove this simp here
        . -- verify that the invariant holds when we flush the system
          use ⟨⟨sj2l, sj2r⟩, sj1l ++ [heq.mp s], sj1r⟩
          apply And.intro
          . apply existSR_reflexive
          . dsimp [φ₃, ψ] at Hψ
            obtain ⟨⟨h, _, _⟩, hₑ⟩ := Hψ
            dsimp [φ₃, ψ]
            and_intros
            . rw [<- List.append_assoc, <- List.append_assoc, h]
            . assumption
            . assumption
            . cases hₑ; constructor
      . unfold rhsModule at a
        rw [PortMap.rw_rule_execution] at a
        dsimp at a
        obtain ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩⟩ := a
        subst_vars
        have_hole heq : ((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_1" }).fst = _ := by dsimp [reducePortMapgetIO]
        use ⟨⟨sj2l, sj2r⟩, ⟨sj1l, sj1r ++ [heq.mp s]⟩⟩
        apply And.intro
        . rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; simp
        . use ⟨⟨sj2l, sj2r⟩, sj1l, sj1r ++ [heq.mp s]⟩
          apply And.intro
          . apply existSR_reflexive
          . dsimp [φ₃, ψ] at Hψ
            obtain ⟨⟨_, h, _⟩, hₑ⟩ := Hψ
            subst_vars
            dsimp [φ₃, ψ]
            and_intros
            . assumption
            . rw [<- List.append_assoc, <- List.append_assoc, h]
            . rfl
            . cases hₑ; constructor
      . unfold rhsModule at a
        rw [PortMap.rw_rule_execution] at a
        dsimp at a
        obtain ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩⟩ := a
        subst_vars
        have_hole heq : ((rhsModule T₁ T₂ T₃).inputs.getIO { inst := InstIdent.top, name := "i_2" }).fst = _ := by dsimp [reducePortMapgetIO]
        use ⟨⟨sj2l, sj2r ++ [heq.mp s]⟩, ⟨sj1l, sj1r⟩⟩
        apply And.intro
        . rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; simp
        . use ⟨⟨sj2l, sj2r ++ [heq.mp s]⟩, sj1l, sj1r⟩
          apply And.intro
          . apply existSR_reflexive
          . dsimp [φ₃, ψ] at Hψ
            obtain ⟨⟨_, _, _⟩, hₑ⟩ := Hψ
            subst_vars
            dsimp [φ₃, ψ]
            and_intros
            . assumption
            . assumption
            . rw [<- List.append_assoc]
            . cases hₑ; constructor
    . exfalso; exact (PortMap.getIO_not_contained_false a HContains)
  -- output rules
  . intro ident i v hrule
    by_cases HContains: ((rhsModule T₁ T₂ T₃).outputs.contains ident)
    . have: ∃ rule, rule ∈ (lhsModule T₁ T₂ T₃).internals := by
        simp [lhsModule]
      obtain ⟨rule, h⟩ := this
      have: ∃ almost_mid_s, rule init_s almost_mid_s := by
        apply (f₁ _ init_i i) at Hψ
        . specialize Hψ hrule
          assumption
        . assumption
      obtain ⟨almost_mid_s, _⟩ := this
      use almost_mid_s
      rw [exists_and_left]
      and_intros
      . apply existSR_single_step' <;> assumption
      . unfold φ₃ at Hψ
        obtain ⟨_, _⟩ := Hψ
        have hₛ: single_internal almost_mid_s := by
          apply f' <;> assumption
        have: existSR (lhsModule T₁ T₂ T₃).internals init_s almost_mid_s := by
          apply existSR_single_step' <;> assumption
        have hψ: ψ init_i almost_mid_s := by
          apply ψ_holds_over_internals_spec <;> assumption
        clear this
        have: ∃ mid_s, ((lhsModule T₁ T₂ T₃).outputs.getIO ident).snd almost_mid_s ↑v mid_s := by
          apply f'' <;> assumption
        obtain ⟨mid_s, _⟩ := this
        use mid_s
        apply And.intro
        . assumption
        . unfold φ₃
          apply And.intro
          . apply outputs_preserves_ψ <;> assumption
          . apply f₃ <;> assumption
    . exfalso; exact (PortMap.getIO_not_contained_false hrule HContains)
  -- internal rules
  . intros
    use init_s
    apply And.intro
    . exact existSR_reflexive
    . dsimp [φ₃] at *
      obtain ⟨_, _⟩ := Hψ
      . apply And.intro
        . apply ψ_holds_over_internals_impl init_i
          . assumption
          . apply existSR_single_step' <;> assumption
        . assumption

---------------------------------------------------------------------------------------------------

-- TODO: Make these cast a coercion
def cast:
  ∀ ident, ((flushed (rhsModule T₁ T₂ T₃)).inputs.getIO ident).fst = ((flushed (lhsModule T₁ T₂ T₃)).inputs.getIO ident).fst :=
by
  intro ident
  have: MatchInterface (flushed (rhsModule T₁ T₂ T₃)) (rhsModule T₁ T₂ T₃) := by infer_instance
  rw [this.input_types ident]
  have: MatchInterface (flushed (lhsModule T₁ T₂ T₃)) (lhsModule T₁ T₂ T₃) := by infer_instance
  rw [this.input_types ident]
  have: MatchInterface (rhsModule T₁ T₂ T₃) (lhsModule T₁ T₂ T₃) := by infer_instance
  exact this.input_types ident

-- TODO: Make these cast a coercion
def cast':
  ∀ ident, ((flushed (rhsModule T₁ T₂ T₃)).outputs.getIO ident).fst = ((flushed (lhsModule T₁ T₂ T₃)).outputs.getIO ident).fst :=
by
  dsimp [flushed]
  have: MatchInterface (rhsModule T₁ T₂ T₃) (lhsModule T₁ T₂ T₃) := by infer_instance
  exact this.output_types

def φ₄ (rhs : rhsModuleType T₁ T₂ T₃) (lhs : lhsModuleType T₁ T₂ T₃) : Prop :=
  ψ rhs lhs ∧ pf (lhsModule T₁ T₂ T₃) lhs

-- TODO: Can I use only ψ?
theorem refines₄:
  flushed (rhsModule T₁ T₂ T₃) ⊑_{φ₄} flushed (lhsModule T₁ T₂ T₃) :=
by
  unfold Module.refines_φ
  intro init_i init_s Hψ
  apply Module.comp_refines.mk
  . -- inputs rules
    intro ident mid_i v h₁
    have: ∃ s', ((flushed (lhsModule T₁ T₂ T₃)).inputs.getIO ident).snd init_s ((cast ident).mp v) s' := by
      apply flhs_can_always_input
      have: MatchInterface (rhsModule T₁ T₂ T₃) (lhsModule T₁ T₂ T₃) := by infer_instance
      apply PortMap.rule_contains at h₁
      rw [flushed_preserves_ports] at h₁
      sorry -- trivial
    obtain ⟨s', h₂⟩ := this
    use s', s'
    apply And.intro
    . assumption
    . apply And.intro
      . apply existSR_reflexive
      . unfold φ₄; apply And.intro
        . apply bll at h₁
          apply bll at h₂
          obtain ⟨s₁, _, _⟩ := h₁
          obtain ⟨s₂, _, _⟩ := h₂
          simp at *
          obtain ⟨_, _⟩ := Hψ
          have: ψ s₁ s₂ := by
            apply inputs_preserves_ψ <;> simpa
          apply ψ_holds_over_internals <;> assumption
        . apply flushed_modules_has_flushed_states <;> assumption
  . -- outputs rules
    intro ident mid_i v h₁
    use init_s
    rw [exists_and_left]
    apply And.intro
    . apply existSR_reflexive
    . obtain ⟨_, _⟩ := Hψ
      have: ∃ s', ((flushed (lhsModule T₁ T₂ T₃)).outputs.getIO ident).snd init_s ((cast' ident).mp v) s' := by
        have: at_least_single_internal init_s := by
          apply f₆ <;> assumption
        dsimp [flushed] at *
        apply f₅ <;> assumption
      obtain ⟨s', _⟩ := this
      use s'
      apply And.intro
      . assumption
      . dsimp [flushed] at *
        unfold φ₄; apply And.intro
        . apply outputs_preserves_ψ <;> assumption
        . apply b₂ <;> assumption
  . --internal rules
    intro rule mid_i h₁ h₂
    use init_s
    apply And.intro
    . apply existSR_reflexive
    . dsimp [flushed] at h₁
      cases h₁

end DataflowRewriter.JoinRewrite
