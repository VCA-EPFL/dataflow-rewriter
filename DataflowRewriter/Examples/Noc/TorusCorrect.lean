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
abbrev spec := (noc dt Data).spec_bag
abbrev specT := (noc dt Data).spec_bagT

theorem route_xy_correct : Noc.Route_correct (noc dt Data) := by
  intros src dst
  dsimp [noc, DirectedTorus.xy_to_noc, DirectedTorus.route_xy]
  intros H
  cases Hx: (dt.get_x src != dt.get_x dst)
  <;> cases Hy: (dt.get_y src != dt.get_y dst)
  <;> simp [Hx, Hy] at H
  <;> simp at Hx Hy
  · sorry -- TODO: annoying arithmetic
  · simp [DirLocal', DirectedTorus.DirY] at H
  · simp [DirLocal'] at H
  · simp [DirLocal'] at H

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
    unfold Noc.mk_router_input Noc.input_rel Noc.mk_spec_bag_input_rule at *
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
      · unfold noc Noc.DirLocal at Hrule2
        obtain H := route_xy_correct dt Data (by unfold noc; rw [Hrule2])
        simpa [H]
      · exists idx'; dsimp at Hidx'; simpa [Hidx']
    · -- TODO: Annoying proof of permutation, seems true
      sorry
  · intros rule mid_i HruleIn Hrule
    exists s
    and_intros
    · constructor
    · unfold φ at *
      dsimp [drcomponents] at HruleIn
      obtain ⟨idx1, idx2, Hij⟩ := RelInt.liftFinf_in HruleIn
      unfold Noc.mk_router_conn at Hij
      rw [mapFinIdx_get] at Hij
      subst rule
      dsimp [drcomponents] at Hrule
      obtain ⟨val, i', ⟨Hval1, Hval2⟩, Hval3⟩ := Hrule
      subst i
      subst mid_i
      apply List.Perm.symm
      apply List.Perm.trans
      · apply List.Perm.symm; exact H
      · -- TODO: Annoying proof of permutation, seems true
        sorry

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
      · unfold noc Noc.DirLocal at Hrule2
        obtain H := route_xy_correct dt Data (by unfold noc; rw [Hrule2])
        simpa [H]
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

def φ (I : (noc dt Data).spec_bagT) (S : (noc dt Data).nocT) : Prop :=
  -- TODO: Wrong, probably
  -- I think the φ might just be that any messages is in the target router,
  -- ready to be extracted with an output rule
  -- This only work because we are in an unbounded spec, meaning we can get all
  -- message to destination always.
  -- This gets more complicated when we are working with bounded arrays, but we
  -- are not there yet
  S.toList.flatten.Perm I

theorem refines_initial :
  Module.refines_initial ((noc dt Data).spec_bag) (mod dt Data) (φ dt Data) := by
    sorry

theorem refines_φ : ((noc dt Data).spec_bag) ⊑_{φ dt Data} (mod dt Data) := by
  intros i s Hφ
  constructor
  · intros ident mid_i v Hrule
    case_transition Hcontains : (Module.inputs ((noc dt Data).spec_bag)), ident,
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
    case_transition Hcontains : (Module.outputs ((noc dt Data).spec_bag)), ident,
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
