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
    dsimp [Noc.mk_router_input, Noc.mk_spec_bag_input_rule]
    intros ident
    simpa [Batteries.AssocList.find?_eq]
  · dsimp [Noc.build, drcomponents]
    simp only [RelIO_mapVal]
    dsimp [Noc.mk_router_output, Noc.mk_spec_bag_output_rule]
    intros ident
    simpa [Batteries.AssocList.find?_eq]

instance (n : Noc) : MatchInterface n.spec_bag n.build := by
  apply MatchInterface_symmetric
  -- TODO: How can I use the definition right above?
  sorry

-- Multi-Queue -----------------------------------------------------------------
-- TODO: Flit are sent ordered per channel
