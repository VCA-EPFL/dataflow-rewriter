/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import DataflowRewriter.Examples.Noc.Lang
import DataflowRewriter.Examples.Noc.BuildModule
import DataflowRewriter.Examples.Noc.Torus
import DataflowRewriter.Examples.Noc.Spec

open Batteries (AssocList)

namespace DataflowRewriter.Noc.DirectedTorus

variable (dt : DirectedTorus)
variable (Data : Type)

def noc := dt.absolute_xy_to_noc Data
abbrev mod := (noc dt Data).build_module
abbrev spec := (noc dt Data).spec_bag
abbrev specT := (noc dt Data).spec_bagT
--
-- theorem route_xy_correct : Noc.Route_correct (noc dt Data) := by
--   intros src dst
--   dsimp [noc, DirectedTorus.xy_to_noc, DirectedTorus.route_xy]
--   intros H
--   cases Hx: (dt.get_x src != dt.get_x dst)
--   <;> cases Hy: (dt.get_y src != dt.get_y dst)
--   <;> simp only [Hx, Hy] at H
--   <;> simp only [bne_eq_false_iff_eq, bne_iff_ne, ne_eq] at Hx Hy
--   · sorry -- TODO: annoying arithmetic
--   · simp [DirLocal', DirectedTorus.DirY] at H
--   · simp [DirLocal'] at H
--   · simp [DirLocal'] at H

namespace ImplementationInSpec

def φ (I : (noc dt Data).nocT) (S : specT dt Data) : Prop :=
  I.toList.flatten ⊆ S

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
      simpa
    · constructor
    · sorry -- rw [List.concat_eq_append]; apply vec_set_concat_perm H
  · intros ident mid_i v Hrule
    case_transition Hcontains : (Module.outputs (mod dt Data)), ident,
     (PortMap.getIO_not_contained_false' Hrule)
    dsimp [drcomponents] at v Hrule Hcontains ⊢
    obtain ⟨idx, Heq⟩ := RelIO.liftFinf_in Hcontains
    subst ident
    rw [PortMap.rw_rule_execution RelIO.liftFinf_get] at Hrule
    dsimp at Hrule
    obtain ⟨head, Hrule1, Hrule2⟩ := Hrule
    subst i
    unfold φ at H
    sorry
    -- obtain ⟨idx', Hidx'⟩ := vec_set_perm_in H
    -- exists s.remove idx'
    -- and_intros
    -- · rw [PortMap.rw_rule_execution RelIO.liftFinf_get]
    --   dsimp only [drcomponents]
    --   and_intros
    --   · unfold noc Noc.DirLocal at Hrule2
    --     obtain H := route_xy_correct dt Data (by unfold noc; rw [Hrule2])
    --     simpa [H]
    --   · exists idx'; dsimp at Hidx'; simpa [Hidx']
    -- · apply vec_set_cons_remove_perm Hidx' H
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
      sorry
      -- apply List.Perm.symm
      -- apply List.Perm.trans
      -- · apply List.Perm.symm; exact H
      -- · apply vec_set_cons_perm

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
      obtain ⟨head, Hrule1, Hrule2⟩ := Hrule
      subst i
      sorry
      -- obtain ⟨idx', Hidx'⟩ := vec_set_perm_in Hφ
      -- exists s.remove idx'
      -- rw [PortMap.rw_rule_execution RelIO.liftFinf_get]
      -- dsimp [drcomponents]
      -- and_intros
      -- -- · sorry
      -- -- unfold noc Noc.DirLocal at Hrule2
      -- --   obtain H := route_xy_correct dt Data (by unfold noc; rw [Hrule2])
      -- --   simpa [H]
      -- · exists idx'; dsimp at Hidx'; and_intros
      --   · rfl
      --   · simp [Hidx']; sorry

theorem correct : (mod dt Data) ⊑ (spec dt Data) := by
  apply (
    Module.refines_φ_refines
      (ϕ_indistinguishable dt Data)
      (refines_initial dt Data)
      (refines_φ dt Data)
  )

end ImplementationInSpec
