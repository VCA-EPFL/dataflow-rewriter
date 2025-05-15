/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import DataflowRewriter.Component
import DataflowRewriter.ExprLow
import DataflowRewriter.ExprLowLemmas
import DataflowRewriter.Module
import DataflowRewriter.ModuleReduction

import DataflowRewriter.Examples.Noc.Basic
import DataflowRewriter.Examples.Noc.BasicLemmas
import DataflowRewriter.Examples.Noc.Components
import DataflowRewriter.Examples.Noc.Implementation.BagRouteNoc

open Batteries (AssocList)

namespace DataflowRewriter.Examples.Noc

variable [P : NocParam]

-- Utilities which does not belong here (TODO: Move elsewhere) -----------------

-- TODO: Find better name, prove
theorem permutation_lemma1 {α} {v : α} {l1 l2 : List α}
  (Heq : l1.Perm (v :: l2)) :
    ∃ i : Fin l1.length, l1[i] = v ∧ (l1.eraseIdx i).Perm l2 := by
    induction l2 generalizing l1
    · simp at Heq; rw [Heq]
      exists (Fin.mk 0 (by simpa))
    · sorry

-- TODO: Find better name, prove
theorem permutation_lemma2 {α} {l l1 l2 l2': List α}
  (Hl : l.Perm (l1 ++ l2)) (Hr : l2.Perm l2') :
  l.Perm (l1 ++ l2') := by sorry

-- TODO: Find better name, prove
theorem permutation_lemma3 {α} {l : List α} {n : Fin l.length} :
  l.Perm (l[n] :: List.eraseIdx l ↑n) := by sorry

-- TODO: Find better name, prove
theorem permutation_lemma4 {α} {l l' : List α} {v} {H : l ∈ List.permutations l'} :
  l.concat v ∈ List.permutations (l'.concat v) := by
    sorry

abbrev typeOf {α} (_ : α) : Type := α

-- Correctness -----------------------------------------------------------------

instance : MatchInterface noc_lowM noc where
  input_types := by
    intros ident
    dsimp [drunfold_defs, drcomponents]
    rw [AssocList.mapKey_map_toAssocList]
    dsimp [drunfold_defs, drcomponents]
    apply (getIO_map_ident_match_1 (Heq := by simpa))
  output_types := by
    intros ident
    dsimp [drunfold_defs, drcomponents]
    rw [AssocList.mapKey_map_toAssocList]
    dsimp [drunfold_defs, drcomponents]
    apply (getIO_map_ident_match_1 (Heq := by simpa))
  inputs_present := by
    intros ident
    dsimp [drunfold_defs, drcomponents]
    rw [AssocList.mapKey_map_toAssocList]
    dsimp [drunfold_defs, drcomponents]
    simp
    apply isSome_same_list
    constructor <;> intros H <;> obtain ⟨x, _, _⟩ := H <;> exists x <;> simpa
  outputs_present := by
    intros ident
    dsimp [drunfold_defs, drcomponents]
    rw [AssocList.mapKey_map_toAssocList]
    dsimp [drunfold_defs, drcomponents]
    simp
    apply isSome_same_list
    constructor <;> intros H <;> obtain ⟨x, _, _⟩ := H <;> exists x <;> simpa

def φ (I : noc_lowT) (S : nocT) : Prop :=
  S.Perm (I.1 ++ I.2)

theorem noc_low_refines_initial :
  Module.refines_initial noc_lowM noc φ := by
    unfold noc_lowM noc noc'
    dsimp [Module.refines_initial, NatModule.stringify, Module.mapIdent]
    intros i Hi
    obtain ⟨Hi1, Hi2⟩ := Hi
    unfold φ
    rw [Hi1, Hi2]
    exists []

theorem noc_low_refines_φ : noc_lowM ⊑_{φ} noc := by
  intros i s H
  constructor
  <;> unfold noc noc' noc_lowM
  <;> intros ident mid_i v Hrule
  <;> dsimp [
    NatModule.stringify, Module.mapIdent,
    InternalPort.map, lift_f, mk_nroute_output_rule
  ] at v Hrule ⊢
  · case_transition Hcontains : (Module.inputs noc_lowM), ident,
     (PortMap.getIO_not_contained_false' Hrule)
    simp [noc_lowM] at Hcontains
    obtain ⟨n, HnFin, _⟩ := Hcontains
    subst ident
    have_hole Hv : typeOf v = _ := by
      unfold typeOf
      rewrite [←NatModule.stringify_input]
      conv =>
        pattern (fun x => _)
        intro x
        rewrite [←NatModule.stringify_input]
    rw [getIO_map_stringify_input] at Hv
    dsimp at Hv
    exists s.concat (Hv.mp v)
    exists s.concat (Hv.mp v)
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
      rw [List.concat_eq_append, ←List.append_assoc, ←List.concat_eq_append]
      sorry
  · case_transition Hcontains : (Module.outputs noc_lowM), ident,
     (PortMap.getIO_not_contained_false' Hrule)
    simp [noc_lowM] at Hcontains
    obtain ⟨n, HnFin, _⟩ := Hcontains
    subst ident
    rw [PortMap.rw_rule_execution
      (h := by apply (getIO_map_stringify_output) <;> rfl)
    ] at Hrule
    dsimp at Hrule
    obtain ⟨⟨Hrule1, Hrule2⟩, Hrule3⟩ := Hrule
    unfold φ at H
    rw [Hrule2, Hrule3] at H
    obtain ⟨index, Hindex1, Hindex2⟩ := permutation_lemma1 H
    exists s.eraseIdx index
    rw [PortMap.rw_rule_execution
      (h := by rw [AssocList.mapKey_map_toAssocList])
    ]
    rw [PortMap.rw_rule_execution
      (h := by apply (getIO_map_stringify_output) <;> rfl)
    ]
    dsimp [lift_f, mk_noc_output_rule] at v ⊢
    split_ands
    · simpa [←Hrule1]
    · exists ↑index;  split_ands
      · rfl
      · sorry
    · exact Hindex2
  · exists s; split_ands
    · constructor
    · simp at v
      subst ident
      obtain ⟨a, b, output, n, ⟨⟨⟨c, H1, H2⟩, H3⟩, H4, H5⟩⟩ := Hrule
      unfold φ
      rw [H4, ←H5, H1, H2]
      unfold φ at H
      rw [H3] at H
      rw [List.append_assoc]
      apply (permutation_lemma2 (Hl := H))
      apply permutation_lemma3

theorem noc_low_ϕ_indistinguishable :
  ∀ i s, φ i s → Module.indistinguishable noc_lowM noc i s := by
    intros i s Hφ
    constructor
    <;> intros ident new_i v Hrule
    <;> unfold noc_lowM at *
    <;> dsimp [drcomponents, drunfold_defs] at v ⊢ Hrule
    <;> have ⟨n, Hn1, Hn2⟩ := getIO_map_ident Hrule
    <;> subst ident
    · have_hole Hv : typeOf v = _ := by
        unfold typeOf
        rewrite [←NatModule.stringify_input]
        conv =>
          pattern (fun x => _)
          intro x
          rewrite [←NatModule.stringify_input]
      rw [getIO_map_stringify_input] at Hv
      dsimp at Hv
      exists s.concat (Hv.mp v)
      rw [PortMap.rw_rule_execution
        (h := by rw [AssocList.mapKey_map_toAssocList])
      ]
      rw [PortMap.rw_rule_execution
        (h := by apply (getIO_map_stringify_input) <;> rfl)
      ] at Hrule ⊢
      dsimp [lift_f, mk_noc_input_rule, mk_nbag_input_rule] at Hrule ⊢
      simpa
    ·
      -- rw [getIO_map_stringify_output] at v
      rw [PortMap.rw_rule_execution
        (h := by apply (getIO_map_stringify_output) <;> rfl)
      ] at Hrule
      dsimp [lift_f, mk_noc_output_rule, mk_nroute_output_rule] at Hrule v
      obtain ⟨⟨Hrule1, Hrule2⟩, Hrule3⟩ := Hrule
      unfold φ at Hφ
      rw [Hrule2, Hrule3] at Hφ
      obtain ⟨index, Hindex1, Hindex2⟩ := permutation_lemma1 Hφ
      exists s.eraseIdx index
      rw [PortMap.rw_rule_execution
        (h := by rewrite [AssocList.mapKey_map_toAssocList]; apply (getIO_map_stringify_output) <;> rfl)
      ]
      dsimp
      split_ands
      · simpa [←Hrule1]
      · exists index; split_ands <;> simpa [←Hindex1]

theorem noc_low_correct : noc_lowM ⊑ noc := by
  apply (
    Module.refines_φ_refines
      noc_low_ϕ_indistinguishable
      noc_low_refines_initial
      noc_low_refines_φ
  )

end DataflowRewriter.Examples.Noc
