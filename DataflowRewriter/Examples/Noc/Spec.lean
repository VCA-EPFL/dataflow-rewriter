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

abbrev spec_bagT (n : Noc) : Type :=
  List n.Flit

@[drcomponents]
def mk_spec_bag_input_rule (n : Noc) (rid : n.RouterID) : RelIO (spec_bagT n) :=
    ⟨n.Flit, λ old_s v new_s => new_s = old_s ++ [v]⟩

@[drcomponents]
def mk_spec_bag_output_rule (n : Noc) (rid : n.RouterID) : RelIO (spec_bagT n) :=
    ⟨
      n.Flit,
      λ oldS v newS =>
        v.2.dst = rid ∧ ∃ i, newS = oldS.remove i ∧ v = oldS.get i
    ⟩

-- Specification of a noc as a bag, all flit are sent unordered
@[drcomponents]
def spec_bag (n : Noc) (name := "spec_bag") : NatModule (NatModule.Named name (spec_bagT n)) :=
  {
    inputs := RelIO.liftFinf n.netsz (mk_spec_bag_input_rule n),
    outputs := RelIO.liftFinf n.netsz (mk_spec_bag_output_rule n),
    init_state := λ s => s = [],
  }

instance (n : Noc) : MatchInterface n.build (spec_bag n) where
  inputs_present := by sorry
  outputs_present := by sorry
  input_types := by sorry
  output_types := by sorry
