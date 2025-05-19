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

def dt_noc := dt.xy_to_noc Data
abbrev dt_mod := (dt_noc dt Data).build
abbrev spec := spec_bag (dt_noc dt Data)
abbrev specT := spec_bagT (dt_noc dt Data)

namespace ImplementationInSpec

def φ (I : (dt_noc dt Data).nocT) (S : specT dt Data) : Prop :=
  I.toList.flatten.Perm S

theorem dt_refines_initial :
  Module.refines_initial (dt_mod dt Data) (spec dt Data) (φ dt Data) := by
    dsimp [drcomponents, Module.refines_initial]
    intros i s
    subst i
    exists []
    and_intros
    · rfl
    · unfold φ; induction (dt_noc dt Data).netsz <;> simpa

theorem dt_refines_φ : (dt_mod dt Data) ⊑_{φ dt Data} (spec dt Data) := by
  intros i s H
  constructor
  · intros ident mid_i v Hrule
    case_transition Hcontains : (Module.inputs (dt_mod dt Data)), ident,
     (PortMap.getIO_not_contained_false' Hrule)
    dsimp [drcomponents] at v Hrule Hcontains ⊢
    obtain ⟨idx, Heq⟩ := RelIO.liftFinf_in Hcontains
    subst ident
    have_hole Hv : typeOf v = _ := by
      unfold typeOf
      rewrite [RelIO.liftFinf_get, Noc.mk_router_input]
      dsimp
    have_hole Htmp : typeOf Hrule = _ := by
      unfold typeOf
      rfl
    unfold Noc.mk_router_input Noc.input_rel mk_spec_bag_input_rule at *
    exists s.concat (Hv.mp v)
    exists s.concat (Hv.mp v)
    and_intros
    · -- rw [RelIO.liftFinf_get]
      sorry
    · constructor
    · unfold φ at *
      sorry
  · intros ident mid_i v Hrule
    case_transition Hcontains : (Module.outputs (dt_mod dt Data)), ident,
     (PortMap.getIO_not_contained_false' Hrule)
    dsimp [drcomponents] at v Hrule Hcontains ⊢
    unfold mk_spec_bag_output_rule
    dsimp
    sorry
  · intros rule mid_i Hrule _
    exists s
    and_intros
    · constructor
    · unfold φ at *
      dsimp [drcomponents] at Hrule
      -- rw [RelInt.liftFinf_in]
      sorry

theorem dt_ϕ_indistinguishable :
  ∀ i s, φ dt Data i s → Module.indistinguishable (dt_mod dt Data) (spec dt Data) i s := by
    intros i s Hφ
    constructor
    <;> intros ident new_i v Hrule
    · case_transition Hcontains : (Module.inputs (dt_mod dt Data)), ident,
       (PortMap.getIO_not_contained_false' Hrule)
      obtain ⟨i, Hi⟩ := RelIO.liftFinf_in Hcontains
      subst ident
      sorry
    · case_transition Hcontains : (Module.outputs (dt_mod dt Data)), ident,
       (PortMap.getIO_not_contained_false' Hrule)
      obtain ⟨i, Hi⟩ := RelIO.liftFinf_in Hcontains
      subst ident
      sorry

theorem dt_correct : (dt_mod dt Data) ⊑ (spec dt Data) := by
  apply (
      Module.refines_φ_refines
        (dt_ϕ_indistinguishable dt Data)
        (dt_refines_initial dt Data)
        (dt_refines_φ dt Data)
    )

end ImplementationInSpec

namespace SpecInImplementation

def φ (I : spec_bagT (dt_noc dt Data)) (S : (dt_noc dt Data).nocT) : Prop :=
  S.toList.flatten.Perm I

-- TODO: MatchInterface but it should be symetric

-- theorem dt_mod_refines_initial :
--   Module.refines_initial (spec_bag (dt_noc dt Data)) (dt_mod dt Data) (φ dt Data) := by

-- theorem dt_mod_refines_φ : (spec_bag (dt_noc dt Data))  ⊑_{φ dt Data} (dt_mod dt Data) := by
  -- sorry

end SpecInImplementation
