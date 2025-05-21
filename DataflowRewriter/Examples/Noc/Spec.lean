/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import DataflowRewriter.Module
import DataflowRewriter.ModuleLemmas
import DataflowRewriter.Component
import DataflowRewriter.Examples.Noc.Lang

set_option autoImplicit false
set_option linter.all false

namespace DataflowRewriter.Noc

-- Bag -------------------------------------------------------------------------
-- Weakest possible specification, where order is not preserved by the Noc

abbrev Noc.spec_bagT (n : Noc) : Type :=
  List n.Flit

@[drcomponents]
def Noc.mk_spec_bag_input_rule (n : Noc) (rid : n.RouterID) : RelIO (n.spec_bagT) :=
  ⟨n.Flit, λ old_s v new_s => new_s = old_s ++ [v]⟩

@[drcomponents]
def Noc.mk_spec_bag_output_rule (n : Noc) (rid : n.RouterID) : RelIO (spec_bagT n) :=
  ⟨
    n.Flit,
    λ oldS v newS =>
      v.2.dst = rid ∧ ∃ i : Fin oldS.length, newS = oldS.remove i ∧ v = oldS.get i
  ⟩

-- Specification of a noc as a bag, all flit are sent unordered
@[drcomponents]
def Noc.spec_bag (n : Noc) (name := "spec_bag") : NatModule (NatModule.Named name (spec_bagT n)) :=
  {
    inputs := RelIO.liftFinf n.netsz n.mk_spec_bag_input_rule,
    outputs := RelIO.liftFinf n.netsz n.mk_spec_bag_output_rule,
    init_state := λ s => s = [],
  }

instance (n : Noc) : MatchInterface n.build n.spec_bag := by
  apply MatchInterface_simpler
  · dsimp [Noc.build, drcomponents]
    simp only [RelIO_mapVal]
    dsimp only [drcomponents]
    intros ident
    simpa [Batteries.AssocList.find?_eq]
  · dsimp [Noc.build, drcomponents]
    simp only [RelIO_mapVal]
    dsimp only [drcomponents]
    intros ident
    simpa [Batteries.AssocList.find?_eq]

instance (n : Noc) : MatchInterface n.spec_bag n.build := by
  apply MatchInterface_symmetric
  exact inferInstance

-- Multi-Queue -----------------------------------------------------------------
-- Flit are sent ordered per channel (one per each input/output pair)

abbrev Noc.spec_mqueueT (n : Noc) : Type :=
  Vector (List n.Flit) (n.netsz * n.netsz)

abbrev Noc.spec_mqueue_idx (n : Noc) (src dst : n.RouterID) : Fin (n.netsz * n.netsz) :=
  Fin.mk (src * n.netsz + dst) (by sorry) -- TODO

@[drcomponents]
def Noc.mk_spec_mqueue_input_rule (n : Noc) (rid : n.RouterID) : RelIO (n.spec_mqueueT) :=
  ⟨n.Flit, λ old_s v new_s =>
    let idx := n.spec_mqueue_idx rid v.2.dst
    new_s = old_s.set idx (old_s[idx] ++ [v])
  ⟩

@[drcomponents]
def Noc.mk_spec_mqueue_output_rule (n : Noc) (rid : n.RouterID) : RelIO (spec_mqueueT n) :=
  ⟨
    n.Flit, λ old_s v new_s =>
      v.2.dst = rid ∧
      ∃ src : n.RouterID,
        let idx := n.spec_mqueue_idx src v.2.dst
        old_s = new_s.set idx (v :: new_s[idx])
  ⟩

@[drcomponents]
def Noc.spec_mqueue (n : Noc) (name := "spec_mqueue") : NatModule (NatModule.Named name (spec_mqueueT n)) :=
  {
    inputs := RelIO.liftFinf n.netsz n.mk_spec_mqueue_input_rule,
    outputs := RelIO.liftFinf n.netsz n.mk_spec_mqueue_output_rule,
    init_state := λ s => s = Vector.replicate (n.netsz * n.netsz) [],
  }

instance (n : Noc) : MatchInterface n.build n.spec_mqueue := by
  apply MatchInterface_simpler
  · dsimp [Noc.build, drcomponents]
    simp only [RelIO_mapVal]
    dsimp only [drcomponents]
    intros ident
    simpa [Batteries.AssocList.find?_eq]
  · dsimp [Noc.build, drcomponents]
    simp only [RelIO_mapVal]
    dsimp only [drcomponents]
    intros ident
    simpa [Batteries.AssocList.find?_eq]

instance (n : Noc) : MatchInterface n.spec_mqueue n.build := by
  apply MatchInterface_symmetric
  exact inferInstance

instance (n : Noc) : MatchInterface n.spec_mqueue n.spec_bag := by
  apply MatchInterface_transitive n.build
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
    obtain ⟨idx, Hidx⟩ := RelIO.liftFinf_in Hcontains
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
    · intros src dst
      dsimp
      intros v' Hv'
      subst mid_i
      unfold φ at Hφ
      specialize Hφ src dst
      dsimp at Hφ
      -- TODO: We need to do a case analysis: Which vector does v belong to in
      -- Hv'? If it is the set one, then we are done and can specialize Hφ,
      -- otherwise we are directly done in Hv'
      -- rw [Vector.getElem_set_self] at Hv'
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
    obtain ⟨Hrule1, src, Hrule2⟩ := Hrule
    apply Exists.intro ?_
    rw [PortMap.rw_rule_execution RelIO.liftFinf_get]
    dsimp [drcomponents]
    and_intros
    · simpa [Hrule1]
    · -- TODO: Annoying but true
      sorry
    · intros src dst
      dsimp
      rw [Hrule2] at Hφ
      specialize Hφ src dst
      dsimp at Hφ
      -- TODO: True by transitivity with Hφ
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
      obtain ⟨Hrule1, src, Hrule2⟩ := Hrule
      subst i
      apply Exists.intro _
      rw [PortMap.rw_rule_execution RelIO.liftFinf_get]
      dsimp [drcomponents]
      and_intros
      · simpa [Hrule1]
      · sorry -- TODO: Annoying but true
      · sorry -- TODO: Solving variable ?

theorem correct : n.spec_mqueue ⊑ n.spec_bag := by
  apply (
    Module.refines_φ_refines
      (ϕ_indistinguishable n)
      (refines_initial n)
      (refines_φ n)
  )

end MQueueInBag
