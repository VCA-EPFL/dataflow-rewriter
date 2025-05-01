/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import Lean
import Init.Data.BitVec.Lemmas
import Qq

import DataflowRewriter.Simp
import DataflowRewriter.Module
import DataflowRewriter.ExprLow
import DataflowRewriter.ExprLowLemmas
import DataflowRewriter.Component
import DataflowRewriter.KernelRefl
import DataflowRewriter.Reduce
import DataflowRewriter.List
import DataflowRewriter.Tactic
import DataflowRewriter.AssocList
import DataflowRewriter.ModuleReduction

import DataflowRewriter.Examples.NoC.Basic
import DataflowRewriter.Examples.NoC.BasicLemmas
import DataflowRewriter.Examples.NoC.Components

open Batteries (AssocList)

namespace DataflowRewriter.NoC

variable [P : NocParam]

-- Implementation --------------------------------------------------------------

def ε_nbag : Env :=
  [
    (s!"Merge' {P.DataS} {P.netsz}", ⟨_, StringModule.merge' P.Data P.netsz⟩),
    (s!"Bag {P.DataS}", ⟨_, StringModule.bag P.Data⟩),
  ].toAssocList

theorem ε_nbag_merge' :
  ε_nbag.find? s!"Merge' {P.DataS} {P.netsz}" = .some ⟨_, StringModule.merge' P.Data P.netsz⟩ := by
    sorry

theorem ε_nbag_bag :
  ε_nbag.find? s!"Bag {P.DataS}" = .some ⟨_, StringModule.bag P.Data⟩ := by
    sorry

@[drcomponents]
def inputGen (i : ℕ) : InternalPort String × InternalPort String :=
  ⟨
    -- Port defined in the Type (Must have inst := InstIdent.top)
    NatModule.stringify_input i,
    -- Internal name, here a top level port
    NatModule.stringify_input i,
  ⟩

@[drcomponents]
def nbag_low : ExprLow String :=
  let merge := ExprLow.base
    {
      input := List.range P.netsz |>.map inputGen |>.toAssocList,
      output := [⟨
        -- Port defined in the Type (Must have inst := InstIdent.top)
        NatModule.stringify_output 0,
        -- Internal name
        { inst := InstIdent.internal "Merge", name := "merge_to_bag_out" }
      ⟩].toAssocList,
    }
    s!"Merge' {P.DataS} {P.netsz}" -- Instance Type
  let bag := ExprLow.base
    {
      input := [⟨
        NatModule.stringify_input 0,
        { inst := InstIdent.internal "Bag", name := "merge_to_bag_in" }
      ⟩].toAssocList,
      output := [⟨
        NatModule.stringify_output 0,
        NatModule.stringify_output 0
      ⟩].toAssocList,
    }
    s!"Bag {P.DataS}"
  ExprLow.connect
    {
      output := {
        inst := InstIdent.internal "Merge",
        name := "merge_to_bag_out"
      },
      input := {
        inst := InstIdent.internal "Bag",
        name := "merge_to_bag_in"
      },
    }
    (ExprLow.product bag merge)

def nbag_lowT : Type := by
  precomputeTac [T| nbag_low, ε_nbag] by
    simp only [nbag_low, drunfold]
    rw [ε_nbag_merge', ε_nbag_bag]
    simp [drunfold, seval, drcompute, drdecide]

theorem inputGen_reverse {n : List _} :
  (n.map inputGen).toAssocList.inverse = (n.map inputGen).toAssocList := by
    sorry

theorem inputGen_filterId_empty {n : List _} :
  (n.map inputGen).toAssocList.filterId = .nil := by
  induction n with
  | nil => rfl
  | cons =>
    dsimp
    rw (occs := [1, 2]) [inputGen]
    rw [AssocList.filterId_cons_eq]; assumption

theorem bijectivePortRenaming_id {n : List _} :
  (n.map inputGen).toAssocList.bijectivePortRenaming = id := by
    ext i
    simp [AssocList.bijectivePortRenaming, inputGen_reverse, inputGen_filterId_empty]

attribute [drcompute]
  AssocList.mapVal
  AssocList.mapVal_mapKey

axiom bijectivePortRenaming_invert {α} [DecidableEq α] {p : AssocList α α} {i : α} (H : p.invertible):
    (p.bijectivePortRenaming i) =
    let map := p.filterId.append p.inverse.filterId
    map.find? i |>.getD i

def_module nbag_lowM : StringModule nbag_lowT :=
  [e| nbag_low, ε_nbag]
  reduction_by
    dsimp -failIfUnchanged [drunfold_defs, nbag_low, ExprHigh.extract, List.foldlM]
    rw [rw_opaque (by simp -failIfUnchanged (disch := simp) only [drcompute]; dsimp)]
    dsimp -failIfUnchanged [drcomponents, ExprLow.build_module, ExprLow.build_module']
    rw [ε_nbag_bag, ε_nbag_merge']
    dsimp [drcomponents]
    dsimp -failIfUnchanged [
      Module.renamePorts,
      Module.mapPorts2,
      Module.mapOutputPorts, Module.mapInputPorts,
      AssocList.filterId,
      AssocList.filter,
      List.inter,
      InternalPort.map
    ]
    simp -failIfUnchanged (disch := simpa) only [drcompute]
    unfold inputGen
    rw [AssocList.bijectivePortRenaming_same]
    dsimp [InternalPort.map, NatModule.stringify_output, NatModule.stringify_input]
    repeat rw [bijectivePortRenaming_invert]

    simp -failIfUnchanged (disch := simpa) only [drcompute]
    dsimp

    -- Simplify product
    dsimp -failIfUnchanged [Module.product, Module.liftL, Module.liftR]
    simp only [AssocList.mapVal_map_toAssocList, Module.liftR]

    -- Simplify connect
    dsimp [Module.connect', Module.liftL, Module.liftR]
    simp -failIfUnchanged (disch := simp) only [
      drcompute,
      drcomponents,
      AssocList.mapVal,
      AssocList.mapVal_mapKey,
      AssocList.bijectivePortRenaming,
      AssocList.invertible,
    ]
    skip
    dsimp -failIfUnchanged [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, AssocList.bijectivePortRenaming, AssocList.invertible, AssocList.keysList, AssocList.inverse, AssocList.filterId, AssocList.filter, List.inter];
    conv =>
     pattern (occs := *) Module.connect'' _ _
     all_goals
      rewrite [(Module.connect''_dep_rw
        (h := by simp -failIfUnchanged (disch := simp) only [
          drcompute,
          drcomponents,
          AssocList.mapVal,
          AssocList.mapVal_mapKey,
          AssocList.bijectivePortRenaming,
          AssocList.invertible]; dsimp -failIfUnchanged)
        (h' := by simp -failIfUnchanged (disch := simp) only [
          drcompute,
          drcomponents,
          AssocList.mapVal,
          AssocList.mapVal_mapKey,
          AssocList.bijectivePortRenaming,
          AssocList.invertible]; dsimp -failIfUnchanged))]
      unfold Module.connect''
      simp only [drcompute]
      dsimp
    skip

-- Correctness -----------------------------------------------------------------
-- TODO: We are currently only trying to prove a refinement in one way, but it
-- would be nice to have a proof of equivalence instead

instance : MatchInterface nbag_lowM (nbag P.Data P.netsz) where
  input_types := by
    intros ident
    unfold nbag_lowM nbag nbag'
    unfold lift_f mk_nbag_input_rule
    dsimp [NatModule.stringify, Module.mapIdent, InternalPort.map, NatModule.stringify_output] at *
    simp [AssocList.mapKey_map_toAssocList, InternalPort.map]
    apply (getIO_map_ident_match_1 (Heq := by intros _; simpa))
  output_types := by
    intros ident
    unfold nbag_lowM nbag nbag'
    dsimp
    by_cases H: (NatModule.stringify_output 0 : InternalPort String) = ident
    <;> simp [*, drunfold, drnat, PortMap.getIO_cons, NatModule.stringify_output, InternalPort.map] at *
    <;> simpa [drcomponents, drcompute, *]
  inputs_present := by
    intros ident
    unfold nbag_lowM nbag nbag'
    simp [NatModule.stringify, Module.mapIdent]
    apply isSome_same_list
    constructor <;> intros H <;> obtain ⟨x, _, _⟩ := H <;> exists x <;> simpa
  outputs_present := by
    intros ident;
    dsimp [nbag_lowM, drcomponents]
    by_cases H: (NatModule.stringify_output 0 : InternalPort String) = ident
    <;> simp [*, drcompute, drunfold, drnat, PortMap.getIO_cons, NatModule.stringify_output, InternalPort.map] at *
    <;> simpa [drcompute, *]

def φ (I : nbag_lowT) (S : List P.Data) : Prop :=
  S = I.fst ++ I.snd

theorem nbag_low_initial_φ :
  Module.refines_initial nbag_lowM (nbag P.Data P.netsz) φ := by
    intros i Hi; exists []; split_ands
    · simpa [drcomponents, drcompute]
    · unfold φ; simpa [Hi]

theorem nbag_low_refines_ϕ : nbag_lowM ⊑_{φ} (nbag P.Data P.netsz) := by
  intros i s H
  constructor
  · intro ident mid_i v Hrule
    case_transition Hcontains : (Module.inputs nbag_lowM), ident,
     (PortMap.getIO_not_contained_false' Hrule)
    simp [nbag_lowM] at Hcontains
    obtain ⟨n, HnFin, Hident⟩ := Hcontains
    subst ident
    unfold nbag nbag'
    dsimp [NatModule.stringify, Module.mapIdent]
    exists (mid_i.1 ++ mid_i.2); exists (mid_i.1 ++ mid_i.2); split_ands
    · rw [PortMap.rw_rule_execution
        (h := by rw [AssocList.mapKey_map_toAssocList])
      ]
      rw [PortMap.rw_rule_execution
        (h := by apply (getIO_map_stringify_input) <;> simpa)
      ] at Hrule ⊢
      subst s
      dsimp [nbag_lowM] at Hrule
      obtain ⟨Hrule1, Hrule2⟩ := Hrule
      simpa [Hrule1, ←Hrule2, lift_f, mk_nbag_input_rule]
    · constructor
    · rfl
  · intro ident mid_i v Hrule
    case_transition Hcontains : (Module.outputs nbag_lowM), ident,
     (PortMap.getIO_not_contained_false' Hrule)
    simp [nbag_lowM] at Hcontains
    subst ident
    obtain ⟨⟨i_1, ⟨H1, H2⟩⟩, Hrule2⟩ := Hrule
    exists mid_i.1 ++ mid_i.2; split_ands
    · unfold nbag nbag'
      dsimp [NatModule.stringify, Module.mapIdent, InternalPort.map, NatModule.stringify_output]
      rw [PortMap.rw_rule_execution]
      dsimp
      subst s
      rw [H1, H2]
      exists Fin.mk i_1 (by simpa [Nat.lt_add_right]); split_ands <;> dsimp
      · simpa [Hrule2, ←eraseIdx_len]
      · apply get_len
    · rfl
  · intros rule mid_i H1 H2;
    simp [nbag_lowM, nbag, nbag', NatModule.stringify, Module.mapIdent] at *
    rw [H1] at H2
    obtain ⟨a, b, output, ⟨⟨H2, H3⟩, H4, H5⟩⟩ := H2
    exists s; split_ands
    · constructor
    · unfold φ
      subst a b s
      simpa [H4, H2]

theorem nbag_low_indistinguishable_φ :
  ∀ x y, φ x y → Module.indistinguishable nbag_lowM (nbag P.Data P.netsz) x y := by
    intros x y Hϕ
    constructor
    <;> intros ident new_i v Hrule
    <;> exists new_i.1 ++ new_i.2
    <;> unfold nbag nbag' nbag_lowM at *
    <;> dsimp at v Hrule
    <;> dsimp [drcomponents]
    <;> subst y
    · rw [PortMap.rw_rule_execution (h := by rw [AssocList.mapKey_map_toAssocList])]
      dsimp [InternalPort.map]
      have ⟨n, Hn1, Hn2⟩ := getIO_map_ident Hrule
      subst ident
      rw [getIO_map_range] at v
      rw [PortMap.rw_rule_execution
        (h := by apply (getIO_map_stringify_input) <;> simpa)
      ] at Hrule ⊢
      dsimp at Hrule v
      simpa [lift_f, mk_nbag_input_rule, Hrule]
      · sorry
    · case_transition Hcontains : (Module.outputs nbag_lowM), ident,
        (PortMap.getIO_not_contained_false' Hrule)
      simp [nbag_lowM] at Hcontains
      subst ident
      rw [PortMap.rw_rule_execution] at Hrule
      dsimp [NatModule.stringify_output] at *
      rw [PortMap.rw_rule_execution (h := by apply PortMap.getIO_cons)];
      dsimp at Hrule ⊢
      obtain ⟨⟨i, Hi1, Hi2⟩, H⟩ := Hrule
      rw [Hi1, Hi2]
      exists Fin.mk i (by simpa [Nat.lt_add_right]); split_ands
      · simpa [←eraseIdx_len, H, Nat.lt_add_right]
      · apply get_len

theorem nbag_low_correct : nbag_lowM ⊑ (nbag P.Data P.netsz) := by
  apply (Module.refines_φ_refines nbag_low_indistinguishable_φ nbag_low_initial_φ nbag_low_refines_ϕ)

end DataflowRewriter.NoC
