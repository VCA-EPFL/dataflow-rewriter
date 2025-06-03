/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import DataflowRewriter.Examples.Noc.Lang
import DataflowRewriter.Examples.Noc.BuildModule
import DataflowRewriter.Examples.Noc.Topology.Torus
import DataflowRewriter.Examples.Noc.Spec
import DataflowRewriter.Examples.Noc.Router

open Batteries (AssocList)

set_option Elab.async false

namespace DataflowRewriter.Noc.RouterIn

  variable (Data : Type) [BEq Data] [LawfulBEq Data]
  variable (noc : Noc Data)
  variable (router' : Router noc.netsz noc.Flit)

  abbrev noc' : Noc Data :=
    {
      topology    := noc.topology
      routing_pol := noc.routing_pol
      routers     := router'
    }

  abbrev nocM := noc.build_module
  abbrev nocM' := (noc' Data noc router').build_module

  variable (router'_ok : ∀ rid, (noc' Data noc router').spec_router rid ⊑ noc.spec_router rid)
  -- TODO: Extract from router'_ok the mm, φ and properties

  def φ (I : (noc' Data noc router').State) (S : noc.State) : Prop :=
    -- Vector.map φ basically?
    sorry

  instance : MatchInterface (nocM' Data noc router') (nocM Data noc) := by
    apply MatchInterface_simpler
    <;> intros ident
    <;> dsimp [drcomponents, drunfold_defs]
    <;> sorry

  theorem refines_initial :
    Module.refines_initial (nocM' Data noc router') (nocM Data noc) (φ Data noc router') := by
      sorry

  theorem refines_φ : (nocM' Data noc router') ⊑_{φ Data noc router'} (nocM Data noc) := by
    sorry

  theorem ϕ_indistinguishable :
    ∀ i s, (φ Data noc router') i s → Module.indistinguishable (nocM' Data noc router') (nocM Data noc) i s := by
      sorry

  theorem correct : (nocM' Data noc router') ⊑ (nocM Data noc) := by
    apply (
      Module.refines_φ_refines
        (ϕ_indistinguishable Data noc router')
        (refines_initial Data noc router')
        (refines_φ Data noc router')
    )

end DataflowRewriter.Noc.RouterIn
