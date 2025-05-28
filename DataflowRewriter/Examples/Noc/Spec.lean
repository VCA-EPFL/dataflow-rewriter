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

variable {Data : Type} [BEq Data] [LawfulBEq Data]

-- Bag -------------------------------------------------------------------------
-- Weakest possible specification, where order is not preserved by the Noc

abbrev Noc.spec_bagT (n : Noc Data) : Type :=
  List (Data × n.topology.RouterID)

@[drcomponents]
def Noc.mk_spec_bag_input_rule (n : Noc Data) (rid : n.topology.RouterID) : RelIO n.spec_bagT :=
  ⟨Data × n.topology.RouterID, λ old_s v new_s => new_s = old_s ++ [v]⟩

@[drcomponents]
def Noc.mk_spec_bag_output_rule (n : Noc Data) (rid : n.topology.RouterID) : RelIO n.spec_bagT :=
  ⟨
    Data,
    λ oldS v newS =>
      ∃ i : Fin oldS.length, newS = oldS.remove i ∧ (v, rid) = oldS.get i
  ⟩

-- Specification of a noc as a bag, all flit are sent unordered
@[drcomponents]
def Noc.spec_bag (n : Noc Data) (name := "spec_bag") : NatModule (NatModule.Named name n.spec_bagT) :=
  {
    inputs := RelIO.liftFinf n.topology.netsz n.mk_spec_bag_input_rule,
    outputs := RelIO.liftFinf n.topology.netsz n.mk_spec_bag_output_rule,
    init_state := λ s => s = [],
  }

instance (n : Noc Data) : MatchInterface n.build_module n.spec_bag := by
  apply MatchInterface_simpler
  <;> simp only [drcomponents, RelIO_mapVal]
  <;> intros _
  <;> exact True.intro

instance (n : Noc Data) : MatchInterface n.spec_bag n.build_module := by
  apply MatchInterface_symmetric
  exact inferInstance

-- Multi-Queue -----------------------------------------------------------------
-- Flit are sent ordered per channel (one per each input/output pair)

abbrev Noc.spec_mqueueT (n : Noc Data) : Type :=
  Vector n.spec_bagT (n.topology.netsz * n.topology.netsz)

abbrev Noc.spec_mqueue_idx (n : Noc Data) (src dst : n.topology.RouterID) : Fin (n.topology.netsz * n.topology.netsz) :=
  Fin.mk (src * n.topology.netsz + dst) (by sorry) -- TODO

@[drcomponents]
def Noc.mk_spec_mqueue_input_rule (n : Noc Data) (rid : n.topology.RouterID) : RelIO n.spec_mqueueT :=
  ⟨
    Data × n.topology.RouterID, λ old_s v new_s =>
      let idx := n.spec_mqueue_idx rid v.2
      new_s = old_s.set idx (old_s[idx] ++ [v])
  ⟩

@[drcomponents]
def Noc.mk_spec_mqueue_output_rule (n : Noc Data) (rid : n.topology.RouterID) : RelIO n.spec_mqueueT :=
  ⟨
    Data, λ old_s v new_s =>
      ∃ src : n.topology.RouterID,
        let idx := n.spec_mqueue_idx src rid
        old_s = new_s.set idx ((v, rid) :: new_s[idx])
  ⟩

@[drcomponents]
def Noc.spec_mqueue (n : Noc Data) (name := "spec_mqueue") : NatModule (NatModule.Named name n.spec_mqueueT) :=
  {
    inputs := RelIO.liftFinf n.topology.netsz n.mk_spec_mqueue_input_rule,
    outputs := RelIO.liftFinf n.topology.netsz n.mk_spec_mqueue_output_rule,
    init_state := λ s => s = Vector.replicate (n.topology.netsz * n.topology.netsz) [],
  }

instance (n : Noc Data) : MatchInterface n.build_module n.spec_mqueue := by
  apply MatchInterface_simpler
  <;> simp only [drcomponents, RelIO_mapVal]
  <;> intros _
  <;> exact True.intro

instance (n : Noc Data) : MatchInterface n.spec_mqueue n.build_module := by
  apply MatchInterface_symmetric
  exact inferInstance

instance (n : Noc Data) : MatchInterface n.spec_mqueue n.spec_bag := by
  apply MatchInterface_transitive n.build_module
  repeat exact inferInstance

instance (n : Noc Data) : MatchInterface n.spec_bag n.spec_mqueue := by
  apply MatchInterface_symmetric
  repeat exact inferInstance

