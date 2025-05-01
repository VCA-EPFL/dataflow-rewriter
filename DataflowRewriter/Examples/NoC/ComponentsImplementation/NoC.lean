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
import DataflowRewriter.ExprHigh
import DataflowRewriter.ExprHighLemmas
import DataflowRewriter.Component
import DataflowRewriter.KernelRefl
import DataflowRewriter.Reduce
import DataflowRewriter.List
import DataflowRewriter.Tactic
import DataflowRewriter.AssocList

import DataflowRewriter.Examples.NoC.Basic
import DataflowRewriter.Examples.NoC.BasicLemmas
import DataflowRewriter.Examples.NoC.Components

open Batteries (AssocList)

namespace DataflowRewriter.Examples.NoC

variable [P : NocParam]

-- Implementation --------------------------------------------------------------

def ε_noc : Env :=
  [
    (s!"NBag {P.DataS} × {FlitHeaderS} {P.netsz}", ⟨_, nbag (P.Data × FlitHeader) P.netsz⟩),
    (s!"NRoute {P.DataS} {P.netsz}", ⟨_, nbranch⟩),
  ].toAssocList

theorem ε_noc_nroute :
  ε_noc.find? s!"NRoute {P.DataS} {P.netsz}" = .some ⟨_, nroute⟩ := by
    sorry

theorem ε_noc_nbag :
  ε_noc.find? s!"NBag {P.DataS} × {FlitHeaderS} {P.netsz}"
  = .some ⟨_, nbag (P.Data × FlitHeader) P.netsz⟩ := by
    sorry

def noc_low' : ExprLow String :=
  let nbag : ExprLow String := ExprLow.base
    {
      input := List.range P.netsz |>.map (λ i => ⟨
        NatModule.stringify_input i,
        NatModule.stringify_input i,
      ⟩) |>.toAssocList,
      output := [⟨
        NatModule.stringify_output 0,
        { inst := InstIdent.internal "NBag", name := NatModule.stringify_output 0 }
      ⟩].toAssocList,
    }
    s!"NBag {P.DataS} × {FlitHeaderS} {P.netsz}"
  let nroute : ExprLow String := ExprLow.base
    {
      input := [⟨
        NatModule.stringify_input 0,
        { inst := InstIdent.internal "NRoute", name := NatModule.stringify_input 0 }
      ⟩].toAssocList,
      output := List.range P.netsz |>.map (λ i => ⟨
        NatModule.stringify_output i,
        NatModule.stringify_output i,
      ⟩) |>.toAssocList,
    }
    s!"NRoute {P.DataS} {P.netsz}"
  ExprLow.connect
  {
    output := { inst := InstIdent.internal "NBag", name := NatModule.stringify_output 0 }
    input := { inst := InstIdent.internal "NRoute", name := NatModule.stringify_input 0 }
  }
  (ExprLow.product nroute nbag)

def noc_lowT : Type := by
  precomputeTac [T| noc_low', ε_noc] by
    simp [drunfold, seval, drdecide, -AssocList.find?_eq]
    rw [ε_noc_nbag, ε_noc_nroute]
    simp [drunfold, seval, drcompute, drdecide, nrouteT]

def noc_lowM : StringModule noc_lowT := by
  precomputeTac [e| noc_low', ε_noc] by
    simp [drunfold, seval, drdecide, -AssocList.find?_eq]
    rw [ε_noc_nbag, ε_noc_nroute]
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq]
    conv =>
      pattern (occs := *) Module.connect'' _ _
      all_goals
        rw [(Module.connect''_dep_rw (h := by simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?]; rfl)
                                     (h' := by simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?]; rfl))]; rfl
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?,AssocList.filter,-Prod.exists]
    unfold Module.connect''
    dsimp
    unfold lift_f
    simp? [
      drunfold,
      Module.liftR,
      Module.liftL,
      AssocList.mapVal_map_toAssocList,
      AssocList.mapKey_map_toAssocList,
      AssocList.mapKey_mapKey,
      AssocList.mapVal_mapKey,
      AssocList.eraseAll_append,
      AssocList.eraseAll_map_neq,
      AssocList.eraseAll_nil,
      AssocList.append_nil,
      AssocList.find?_append,
      AssocList.find?_map_neq,
      AssocList.bijectivePortRenaming_same,
      -AssocList.find?_eq,
      InternalPort.map,
      stringify_output_neq,
      stringify_input_neq,
      internalport_neq
    ]
    -- TODO: Make this not ugly and actually portable
    conv =>
      pattern (occs := *) And _ _
      all_goals congr
      rfl
      rfl
      rfl
      rfl
      rw [PortMap.rw_rule_execution
        (h := by simp [
          Module.liftR,
          Module.liftL,
          AssocList.mapVal_map_toAssocList,
          AssocList.mapKey_map_toAssocList,
          AssocList.mapKey_mapKey,
          AssocList.mapVal_mapKey,
          AssocList.eraseAll_append,
          AssocList.eraseAll_map_neq,
          AssocList.eraseAll_nil,
          AssocList.append_nil,
          AssocList.find?_append,
          AssocList.find?_map_neq,
          AssocList.bijectivePortRenaming_same,
          -AssocList.find?_eq,
          InternalPort.map,
          stringify_output_neq,
          stringify_input_neq,
          internalport_neq,
        ]
        <;> rfl)
      ]
      dsimp
      all_goals rfl
    skip

-- Utilities which does not belong here (TODO: Move elsewhere) -----------------

-- TODO: Find better name, prove
theorem permutation_lemma1 {α} {v : α} {l1 l2 : List α}
  (Heq : l1 ∈ List.permutations (v :: l2)) :
    ∃ i : Fin l1.length, l1[i] = v ∧ l1.eraseIdx i ∈ List.permutations l2 := by
    induction l2 generalizing l1
    · simp at Heq; rw [Heq]
      exists (Fin.mk 0 (by simpa))
      simpa
    · sorry

-- TODO: Find better name, prove
theorem permutation_lemma2 {α} {l l1 l2 l2': List α}
  (Hleft : l ∈ (l1 ++ l2).permutations)
  (Hright : l2 ∈ l2'.permutations) :
  l ∈ (l1 ++ l2').permutations := by sorry

-- TODO: Find better name, prove
theorem permutation_lemma3 {α} {l : List α} {n : Fin l.length} :
  l ∈ (l[n] :: List.eraseIdx l ↑n).permutations := by sorry

-- TODO: Find better name, prove
theorem permutation_lemma4 {α} {l l' : List α} {v} {H : l ∈ List.permutations l'} :
  l.concat v ∈ List.permutations (l'.concat v) := by
    sorry

def typeOf {α} (_ : α) : Type := α

-- Correctness -----------------------------------------------------------------

instance : MatchInterface noc_lowM noc where
  input_types := by
    intros ident
    dsimp [
      noc_lowM, noc, noc',
      NatModule.stringify, Module.mapIdent, InternalPort.map,
      NatModule.stringify_input, NatModule.stringify_output,
    ]
    rw [AssocList.mapKey_map_toAssocList]
    dsimp [
      NatModule.stringify, Module.mapIdent, InternalPort.map,
      NatModule.stringify_input, NatModule.stringify_output,
      lift_f, mk_noc_input_rule, mk_nbag_input_rule
    ]
    apply (getIO_map_ident_match_1 (Heq := by simpa))
  output_types := by
    intros ident
    dsimp [
      noc_lowM, noc, noc',
      NatModule.stringify, Module.mapIdent, InternalPort.map,
      NatModule.stringify_input, NatModule.stringify_output,
    ]
    rw [AssocList.mapKey_map_toAssocList]
    dsimp [
      NatModule.stringify, Module.mapIdent, InternalPort.map,
      NatModule.stringify_input, NatModule.stringify_output,
      lift_f, mk_noc_output_rule, mk_nroute_output_rule
    ]
    apply (getIO_map_ident_match_1 (Heq := by simpa))
  inputs_present := by
    intros ident
    unfold noc_lowM noc noc'
    dsimp [
      NatModule.stringify, Module.mapIdent,
      mk_nroute_output_rule,
      mk_noc_output_rule
    ]
    rw [AssocList.mapKey_map_toAssocList]
    dsimp [InternalPort.map, lift_f, mk_noc_output_rule]
    simp
    apply isSome_same_list
    constructor <;> intros H <;> obtain ⟨x, _, _⟩ := H <;> exists x <;> simpa
  outputs_present := by
    intros ident
    unfold noc_lowM noc noc'
    dsimp [
      NatModule.stringify, Module.mapIdent,
      mk_nroute_output_rule,
      mk_noc_output_rule
    ]
    rw [AssocList.mapKey_map_toAssocList]
    dsimp [InternalPort.map, lift_f, mk_noc_output_rule]
    simp
    apply isSome_same_list
    constructor <;> intros H <;> obtain ⟨x, _, _⟩ := H <;> exists x <;> simpa

def φ (I : noc_lowT) (S : nocT) : Prop :=
  ∃ I' ∈ List.permutations (I.1 ++ I.2), S = I'

theorem noc_low_refines_initial :
  Module.refines_initial noc_lowM noc φ := by
    unfold noc_lowM noc noc'
    dsimp [Module.refines_initial, NatModule.stringify, Module.mapIdent]
    intros i Hi
    obtain ⟨Hi1, Hi2⟩ := Hi
    unfold φ
    rw [Hi1, Hi2]
    exists []; simpa

theorem noc_low_refines_φ : noc_lowM ⊑_{φ} noc := by
  intros i s H
  constructor
  <;> unfold noc noc' noc_lowM
  <;> intros ident mid_i v Hrule
  <;> dsimp [
    NatModule.stringify, Module.mapIdent,
    InternalPort.map, lift_f, mk_nroute_output_rule
  ] at v Hrule ⊢
  <;> obtain ⟨i', Hi'1, Hi'2⟩ := H
  <;> subst s
  · case_transition Hcontains : (Module.inputs noc_lowM), ident,
     (fun x => PortMap.getIO_not_contained_false' x Hrule)
    simp [noc_lowM] at Hcontains
    obtain ⟨n, HnFin, _⟩ := Hcontains
    subst ident
    have_hole Hv : typeOf v = _ := by
      unfold typeOf
      rewrite [getIO_map_stringify_input]
      dsimp [mk_nbag_input_rule]
    exists i'.concat (Hv.mp v)
    exists i'.concat (Hv.mp v)
    rw [PortMap.rw_rule_execution
      (h := by rw [AssocList.mapKey_map_toAssocList])
    ]
    rw [PortMap.rw_rule_execution
      (h := by apply (getIO_map_stringify_input) <;> rfl)
    ] at Hrule ⊢
    dsimp [lift_f, mk_noc_input_rule, mk_nbag_input_rule] at v Hrule ⊢
    obtain ⟨Hrule1, Hrule2⟩ := Hrule
    split_ands
    · simpa
    · constructor
    · unfold φ; rw [Hrule1, ←Hrule2]
      exists i'.concat (Hv.mp v)
      split_ands
      · rw [List.concat_eq_append, ←List.append_assoc, ←List.concat_eq_append]
        apply (permutation_lemma4 (H := Hi'1))
      · simpa
  · case_transition Hcontains : (Module.outputs noc_lowM), ident,
     (fun x => PortMap.getIO_not_contained_false' x Hrule)
    simp [noc_lowM] at Hcontains
    obtain ⟨n, HnFin, _⟩ := Hcontains
    subst ident
    rw [PortMap.rw_rule_execution
      (h := by apply (getIO_map_stringify_output) <;> rfl)
    ] at Hrule
    dsimp at Hrule
    obtain ⟨Hrule1, Hrule2⟩ := Hrule
    rw [Hrule1, Hrule2] at Hi'1
    obtain ⟨index, Hindex1, Hindex2⟩ := permutation_lemma1 Hi'1
    exists i'.eraseIdx index
    rw [PortMap.rw_rule_execution
      (h := by rw [AssocList.mapKey_map_toAssocList])
    ]
    rw [PortMap.rw_rule_execution
      (h := by apply (getIO_map_stringify_output) <;> rfl)
    ]
    dsimp [lift_f, mk_noc_output_rule] at v ⊢
    split_ands
    · exists index; simpa [←Hindex1]
    · exists i'.eraseIdx ↑index
  · exists i'; split_ands
    · constructor
    · simp at v
      subst ident
      obtain ⟨a, b, output, ⟨⟨n, H1, H2⟩, H3⟩, ⟨H4, H5⟩⟩ := Hrule
      unfold φ
      exists i'; split_ands
      · rw [H4, ←H5, H1, H2]
        rw [H3] at Hi'1
        rw [List.append_assoc]
        apply (permutation_lemma2 (l := i')
          (Hleft := Hi'1)
          (Hright := by apply permutation_lemma3)
        )
      · rfl

theorem noc_low_ϕ_indistinguishable :
  ∀ i s, φ i s → Module.indistinguishable noc_lowM noc i s := by
    intros i s Hφ
    constructor
    <;> intros ident new_i v Hrule
    <;> unfold noc noc' noc_lowM at *
    <;> dsimp at v Hrule
    <;> dsimp [NatModule.stringify, Module.mapIdent]
    <;> obtain ⟨i', Hi'1, Hi'2⟩ := Hφ
    <;> have ⟨n, Hn1, Hn2⟩ := getIO_map_ident Hrule
    <;> subst s ident
    · have_hole Hv : typeOf v = _ := by
        unfold typeOf
        rewrite [getIO_map_stringify_input]
        dsimp [mk_nbag_input_rule]
      exists i'.concat (Hv.mp v)
      rw [PortMap.rw_rule_execution
        (h := by rw [AssocList.mapKey_map_toAssocList])
      ]
      rw [PortMap.rw_rule_execution
        (h := by apply (getIO_map_stringify_input) <;> rfl)
      ] at Hrule ⊢
      dsimp [lift_f, mk_noc_input_rule, mk_nbag_input_rule] at Hrule ⊢
      simpa
    · rw [getIO_map_stringify_output] at v
      rw [PortMap.rw_rule_execution
        (h := by apply (getIO_map_stringify_output) <;> rfl)
      ] at Hrule
      dsimp [lift_f, mk_noc_output_rule, mk_nroute_output_rule] at Hrule v
      obtain ⟨Hrule1, Hrule2⟩ := Hrule
      rw [Hrule1, Hrule2] at Hi'1
      obtain ⟨index, Hindex1, Hindex2⟩ := permutation_lemma1 Hi'1
      exists i'.eraseIdx index
      rw [PortMap.rw_rule_execution
        (h := by rw [AssocList.mapKey_map_toAssocList])
      ]
      rw [PortMap.rw_rule_execution
        (h := by apply (getIO_map_stringify_output) <;> rfl)
      ]
      dsimp [lift_f, mk_noc_output_rule, mk_nroute_output_rule]
      exists index; split_ands <;> simpa [←Hindex1]

theorem noc_low_correct : noc_lowM ⊑ noc := by
  apply (
    Module.refines_φ_refines
      noc_low_ϕ_indistinguishable
      noc_low_refines_initial
      noc_low_refines_φ
  )

end DataflowRewriter.Examples.NoC
