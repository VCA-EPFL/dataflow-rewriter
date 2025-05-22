/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import DataflowRewriter.Module
import DataflowRewriter.ModuleLemmas
import DataflowRewriter.Component
import DataflowRewriter.Examples.Noc.Lang
import DataflowRewriter.Examples.Noc.BuildModule

set_option autoImplicit false
set_option linter.all false

namespace DataflowRewriter.Noc

-- Bag -------------------------------------------------------------------------
-- Weakest possible specification, where order is not preserved by the Noc

abbrev Noc.spec_bagT (n : Noc) : Type :=
  List (n.Data × n.RouterID)

@[drcomponents]
def Noc.mk_spec_bag_input_rule (n : Noc) (rid : n.RouterID) : RelIO (n.spec_bagT) :=
  ⟨n.Data × n.RouterID, λ old_s v new_s => new_s = old_s ++ [v]⟩

@[drcomponents]
def Noc.mk_spec_bag_output_rule (n : Noc) (rid : n.RouterID) : RelIO (spec_bagT n) :=
  ⟨
    n.Data,
    λ oldS v newS =>
      ∃ i : Fin oldS.length, newS = oldS.remove i ∧ (v, rid) = oldS.get i
  ⟩

-- Specification of a noc as a bag, all flit are sent unordered
@[drcomponents]
def Noc.spec_bag (n : Noc) (name := "spec_bag") : NatModule (NatModule.Named name (spec_bagT n)) :=
  {
    inputs := RelIO.liftFinf n.netsz n.mk_spec_bag_input_rule,
    outputs := RelIO.liftFinf n.netsz n.mk_spec_bag_output_rule,
    init_state := λ s => s = [],
  }

instance (n : Noc) : MatchInterface n.build_module n.spec_bag := by
  apply MatchInterface_simpler
  <;> simp only [drcomponents, RelIO_mapVal]
  <;> intros _
  <;> exact True.intro

instance (n : Noc) : MatchInterface n.spec_bag n.build_module := by
  apply MatchInterface_symmetric
  exact inferInstance

-- Multi-Queue -----------------------------------------------------------------
-- Flit are sent ordered per channel (one per each input/output pair)

abbrev Noc.spec_mqueueT (n : Noc) : Type :=
  Vector n.spec_bagT (n.netsz * n.netsz)

abbrev Noc.spec_mqueue_idx (n : Noc) (src dst : n.RouterID) : Fin (n.netsz * n.netsz) :=
  Fin.mk (src * n.netsz + dst) (by sorry) -- TODO

@[drcomponents]
def Noc.mk_spec_mqueue_input_rule (n : Noc) (rid : n.RouterID) : RelIO (n.spec_mqueueT) :=
  ⟨n.Data × n.RouterID, λ old_s v new_s =>
    let idx := n.spec_mqueue_idx rid v.2
    new_s = old_s.set idx (old_s[idx] ++ [v])
  ⟩

@[drcomponents]
def Noc.mk_spec_mqueue_output_rule (n : Noc) (rid : n.RouterID) : RelIO (spec_mqueueT n) :=
  ⟨
    n.Data, λ old_s v new_s =>
      ∃ src : n.RouterID,
        let idx := n.spec_mqueue_idx src rid
        old_s = new_s.set idx ((v, rid) :: new_s[idx])
  ⟩

@[drcomponents]
def Noc.spec_mqueue (n : Noc) (name := "spec_mqueue") : NatModule (NatModule.Named name (spec_mqueueT n)) :=
  {
    inputs := RelIO.liftFinf n.netsz n.mk_spec_mqueue_input_rule,
    outputs := RelIO.liftFinf n.netsz n.mk_spec_mqueue_output_rule,
    init_state := λ s => s = Vector.replicate (n.netsz * n.netsz) [],
  }

instance (n : Noc) : MatchInterface n.build_module n.spec_mqueue := by
  apply MatchInterface_simpler
  <;> simp only [drcomponents, RelIO_mapVal]
  <;> intros _
  <;> exact True.intro

instance (n : Noc) : MatchInterface n.spec_mqueue n.build_module := by
  apply MatchInterface_symmetric
  exact inferInstance

instance (n : Noc) : MatchInterface n.spec_mqueue n.spec_bag := by
  apply MatchInterface_transitive n.build_module
  repeat exact inferInstance

section MQueueInBag

variable (n : Noc)

def φ (I : n.spec_mqueueT) (S : n.spec_bagT) : Prop :=
  ∀ (src : n.RouterID) (dst : n.RouterID),
    let idx := n.spec_mqueue_idx src dst
    I[idx] ⊆ S

theorem refines_initial :
  Module.refines_initial n.spec_mqueue n.spec_bag (φ n) := by
    dsimp [Module.refines_initial, drcomponents]
    intros i Hi
    subst i
    exists []
    split_ands
    · rfl
    · intros src dst idx v Hv; simp at Hv

theorem refines_φ : n.spec_mqueue ⊑_{φ n} n.spec_bag := by
  intros i s Hφ
  constructor
  · intros ident mid_i v Hrule
    case_transition Hcontains : (Module.inputs n.spec_mqueue), ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp [drcomponents] at *
    obtain ⟨src, Hsrc⟩ := RelIO.liftFinf_in Hcontains
    subst ident
    rw [PortMap.rw_rule_execution RelIO.liftFinf_get] at Hrule
    dsimp [drcomponents] at Hrule
    have_hole Hv : typeOf v = _ := by
      unfold typeOf
      rewrite [Noc.spec_mqueue, RelIO.liftFinf_get]
      dsimp [drcomponents]
    exists s.concat (Hv.mp v)
    exists s.concat (Hv.mp v)
    and_intros
    · rw [PortMap.rw_rule_execution RelIO.liftFinf_get]
      simpa [drcomponents]
    · constructor
    · intros src' dst'
      dsimp
      intros v' Hv'
      subst mid_i
      unfold φ at Hφ
      specialize Hφ src' dst'
      dsimp at Hφ
      by_cases Heq : (↑src' * n.netsz + ↑dst') = (↑src * n.netsz + ↑(Hv.mp v).2)
      · simp only [
          Heq, typeOf, eq_mp_eq_cast, Vector.getElem_set_self, List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false
        ] at Hv'
        simp only [Heq, typeOf, eq_mp_eq_cast] at Hφ
        cases Hv'
        · rename_i Hin;
          simp only [
            List.concat_eq_append, List.mem_append, List.mem_cons,
            List.not_mem_nil, or_false
          ]
          left; exact Hφ Hin
        · rename_i Heq; simp [Heq]
      · -- TODO: We have to say that getting an element of a vector in another
        -- position of where it has been modified is just like accessing the vector
        -- directly
        sorry
  · intros ident mid_i v Hrule
    case_transition Hcontains : (Module.outputs n.spec_mqueue), ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp [drcomponents] at *
    obtain ⟨idx, Hidx⟩ := RelIO.liftFinf_in Hcontains
    subst ident
    rw [PortMap.rw_rule_execution RelIO.liftFinf_get] at Hrule
    dsimp [drcomponents] at Hrule
    have_hole Hv : typeOf v = _ := by
      unfold typeOf
      rewrite [Noc.spec_mqueue, RelIO.liftFinf_get]
      dsimp [drcomponents]
    obtain ⟨src, Hrule⟩ := Hrule
    apply Exists.intro ?_
    rw [PortMap.rw_rule_execution RelIO.liftFinf_get]
    dsimp [drcomponents]
    and_intros
    · -- TODO
      sorry
    · intros src dst
      dsimp
      -- TODO
      sorry
    · sorry -- TODO: Solving variable
  · intros rule mid_i Hcontains Hrule
    exists s

theorem ϕ_indistinguishable :
  ∀ i s, φ n i s → Module.indistinguishable n.spec_mqueue n.spec_bag i s := by
    intros i s Hφ
    constructor <;> intros ident new_i v Hrule <;> dsimp [drcomponents] at *
    · case_transition Hcontains : (Module.inputs n.spec_mqueue), ident,
        (PortMap.getIO_not_contained_false' Hrule)
      dsimp [drcomponents] at *
      obtain ⟨idx, Hidx⟩ := RelIO.liftFinf_in Hcontains
      subst ident
      rw [PortMap.rw_rule_execution RelIO.liftFinf_get] at Hrule
      dsimp [drcomponents] at Hrule
      have_hole Hv : typeOf v = _ := by
        unfold typeOf
        rewrite [Noc.spec_mqueue, RelIO.liftFinf_get]
        dsimp [drcomponents]
      apply Exists.intro _
      · rw [PortMap.rw_rule_execution RelIO.liftFinf_get]
        dsimp [drcomponents]
    · case_transition Hcontains : (Module.outputs n.spec_mqueue), ident,
        (PortMap.getIO_not_contained_false' Hrule)
      dsimp [drcomponents] at *
      obtain ⟨idx, Hidx⟩ := RelIO.liftFinf_in Hcontains
      subst ident
      rw [PortMap.rw_rule_execution RelIO.liftFinf_get] at Hrule
      dsimp [drcomponents] at Hrule
      have_hole Hv : typeOf v = _ := by
        unfold typeOf
        rewrite [Noc.spec_mqueue, RelIO.liftFinf_get]
        dsimp [drcomponents]
      obtain ⟨src, Hrule⟩ := Hrule
      subst i
      apply Exists.intro _
      rw [PortMap.rw_rule_execution RelIO.liftFinf_get]
      dsimp [drcomponents]
      and_intros
      · sorry -- TODO: Annoying but true
      · sorry -- TODO: Solving variable

theorem correct : n.spec_mqueue ⊑ n.spec_bag := by
  apply (
    Module.refines_φ_refines
      (ϕ_indistinguishable n)
      (refines_initial n)
      (refines_φ n)
  )

end MQueueInBag
