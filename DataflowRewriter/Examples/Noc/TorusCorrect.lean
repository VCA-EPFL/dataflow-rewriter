/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import DataflowRewriter.Examples.Noc.Lang
import DataflowRewriter.Examples.Noc.Torus
import DataflowRewriter.Examples.Noc.Spec

open Batteries (AssocList)

namespace DataflowRewriter.Noc.DirectedTorus

variable (dt : DirectedTorus)
variable (Data : Type)

def noc := dt.xy_to_noc Data
abbrev mod := (noc dt Data).build
abbrev spec := spec_bag (noc dt Data)
abbrev specT := spec_bagT (noc dt Data)

namespace ImplementationInSpec

def φ (I : (noc dt Data).nocT) (S : specT dt Data) : Prop :=
  I.toList.flatten.Perm S

theorem refines_initial :
  Module.refines_initial (mod dt Data) (spec dt Data) (φ dt Data) := by
    dsimp [drcomponents, Module.refines_initial]
    intros i s
    subst i
    exists []
    and_intros
    · rfl
    · unfold φ; induction (noc dt Data).netsz <;> simpa

theorem refines_φ : (mod dt Data) ⊑_{φ dt Data} (spec dt Data) := by
  intros i s H
  constructor
  · intros ident mid_i v Hrule
    case_transition Hcontains : (Module.inputs (mod dt Data)), ident,
     (PortMap.getIO_not_contained_false' Hrule)
    dsimp [drcomponents] at v Hrule Hcontains ⊢
    obtain ⟨idx, Hidx⟩ := RelIO.liftFinf_in Hcontains
    subst ident
    have_hole Hv : typeOf v = _ := by
      unfold typeOf
      rewrite [RelIO.liftFinf_get, Noc.mk_router_input]
      dsimp
    rw [PortMap.rw_rule_execution RelIO.liftFinf_get] at Hrule
    dsimp [Noc.mk_router_input, Noc.input_rel] at Hrule
    subst mid_i
    unfold Noc.mk_router_input Noc.input_rel mk_spec_bag_input_rule at *
    exists s.concat (Hv.mp v)
    exists s.concat (Hv.mp v)
    and_intros
    · rw [PortMap.rw_rule_execution RelIO.liftFinf_get]
      simp
    · constructor
    · rw [List.concat_eq_append]; apply vec_set_perm H
  · intros ident mid_i v Hrule
    case_transition Hcontains : (Module.outputs (mod dt Data)), ident,
     (PortMap.getIO_not_contained_false' Hrule)
    dsimp [drcomponents] at v Hrule Hcontains ⊢
    obtain ⟨idx, Heq⟩ := RelIO.liftFinf_in Hcontains
    subst ident
    rw [PortMap.rw_rule_execution RelIO.liftFinf_get] at Hrule
    dsimp at Hrule
    obtain ⟨Hrule1, Hrule2⟩ := Hrule
    subst i
    unfold φ at H
    obtain ⟨idx', Hidx'⟩ := vec_set_perm_in H
    exists s.remove idx'
    and_intros
    · rw [PortMap.rw_rule_execution RelIO.liftFinf_get]
      dsimp only [drcomponents]
      and_intros
      · sorry -- TODO: Arbiter_correct
      · exists idx'; dsimp at Hidx'; simpa [Hidx']
    · sorry -- TODO: Annoying proof of permutation
  · intros rule mid_i Hrule _
    exists s
    and_intros
    · constructor
    · unfold φ at *
      dsimp [drcomponents] at Hrule
      -- rw [RelInt.liftFinf_in]
      sorry -- TODO

theorem ϕ_indistinguishable :
  ∀ i s, φ dt Data i s → Module.indistinguishable (mod dt Data) (spec dt Data) i s := by
    intros i s Hφ
    constructor
    <;> intros ident new_i v Hrule
    · case_transition Hcontains : (Module.inputs (mod dt Data)), ident,
       (PortMap.getIO_not_contained_false' Hrule)
      obtain ⟨idx, Hidx⟩ := RelIO.liftFinf_in Hcontains
      subst ident
      dsimp [drcomponents] at Hrule v ⊢
      rw [PortMap.rw_rule_execution RelIO.liftFinf_get] at Hrule
      dsimp [drcomponents] at Hrule
      have_hole Hv : typeOf v = _ := by
        unfold typeOf
        rewrite [RelIO.liftFinf_get, Noc.mk_router_input]
        dsimp
      exists s.concat (Hv.mp v)
      rw [PortMap.rw_rule_execution RelIO.liftFinf_get]
      simpa [drcomponents]
    · case_transition Hcontains : (Module.outputs (mod dt Data)), ident,
       (PortMap.getIO_not_contained_false' Hrule)
      obtain ⟨idx, Hidx⟩ := RelIO.liftFinf_in Hcontains
      subst ident
      dsimp [drcomponents] at Hrule v ⊢
      rw [PortMap.rw_rule_execution RelIO.liftFinf_get] at Hrule
      dsimp [drcomponents] at Hrule
      have_hole Hv : typeOf v = _ := by
        unfold typeOf
        rewrite [RelIO.liftFinf_get]
        dsimp
      obtain ⟨Hrule1, Hrule2⟩ := Hrule
      subst i
      obtain ⟨idx', Hidx'⟩ := vec_set_perm_in Hφ
      exists s.remove idx'
      rw [PortMap.rw_rule_execution RelIO.liftFinf_get]
      dsimp [drcomponents]
      and_intros
      · sorry -- TODO: Arbiter_correct
      · exists idx'; dsimp at Hidx'; simpa [Hidx']

theorem correct : (mod dt Data) ⊑ (spec dt Data) := by
  apply (
    Module.refines_φ_refines
      (ϕ_indistinguishable dt Data)
      (refines_initial dt Data)
      (refines_φ dt Data)
  )

end ImplementationInSpec

namespace SpecInImplementation

def φ (I : spec_bagT (noc dt Data)) (S : (noc dt Data).nocT) : Prop :=
  -- TODO: Wrong, probably
  S.toList.flatten.Perm I

-- TODO: MatchInterface but it should be symetric

theorem refines_initial :
  Module.refines_initial (spec_bag (noc dt Data)) (mod dt Data) (φ dt Data) := by
    sorry

theorem refines_φ : (spec_bag (noc dt Data)) ⊑_{φ dt Data} (mod dt Data) := by
  intros i s Hφ
  constructor
  · intros ident mid_i v Hrule
    case_transition Hcontains : (Module.inputs (spec_bag (noc dt Data))), ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp [drcomponents] at *
    obtain ⟨idx, Hidx⟩ := RelIO.liftFinf_in Hcontains
    subst ident
    rw [PortMap.rw_rule_execution RelIO.liftFinf_get] at Hrule
    dsimp [drcomponents] at Hrule
    subst mid_i
    skip
    apply Exists.intro _
    apply Exists.intro _
    and_intros
    · rw [PortMap.rw_rule_execution RelIO.liftFinf_get]
      dsimp [drcomponents]
    · apply existSR.done
    · sorry
  · intros ident mid_i v Hrule
    case_transition Hcontains : (Module.outputs (spec_bag (noc dt Data))), ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp [drcomponents] at *
    obtain ⟨rid, Hrid⟩ := RelIO.liftFinf_in Hcontains
    subst ident
    rw [PortMap.rw_rule_execution RelIO.liftFinf_get] at Hrule
    dsimp [drcomponents] at Hrule
    obtain ⟨Hrule1, idx, Hidx1, Hidx2⟩ := Hrule
    subst mid_i
    skip
    apply Exists.intro _
    and_intros
    · rw [PortMap.rw_rule_execution RelIO.liftFinf_get]
      dsimp [drcomponents]
      and_intros
      · sorry
      · sorry
      · sorry
    · sorry
  · sorry

theorem ϕ_indistinguishable :
  ∀ i s, φ dt Data i s → Module.indistinguishable (spec dt Data) (mod dt Data) i s := by
    sorry

theorem correct : (spec dt Data) ⊑ (mod dt Data) := by
  apply (
    Module.refines_φ_refines
      (ϕ_indistinguishable dt Data)
      (refines_initial dt Data)
      (refines_φ dt Data)
  )

end SpecInImplementation
