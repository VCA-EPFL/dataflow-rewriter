/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

-- A bunch of random stuff which doesn't quite fit with the rest

import DataflowRewriter.Module
import DataflowRewriter.Component

open Batteries (AssocList)

namespace DataflowRewriter.Noc

@[simp] abbrev typeOf {α} (_ : α) := α

def fin_range (sz : Nat) : List (Fin sz) :=
  List.replicate sz 0
  |>.mapFinIdx (λ i _ h => Fin.mk i (by rwa [List.length_replicate] at h))

-- RelIO -----------------------------------------------------------------------

@[simp] abbrev RelIO (S : Type) := Σ T : Type, S → T → S → Prop

def RelIO.liftFinf {α : Type _} (n : Nat) (f : Fin n → α) : PortMap Nat α :=
  fin_range n |>.map (λ i => ⟨↑i.toNat, f i⟩) |>.toAssocList

theorem RelIO.liftFinf_in {S} {ident : InternalPort Nat} {n : Nat} {f : Fin n → RelIO S}:
  AssocList.contains ident (RelIO.liftFinf n f) = true
  → ∃ i : Fin n, ident = i := by
      dsimp [liftFinf, fin_range]
      simp only [
        AssocList.contains_eq, List.toList_toAssocList, List.any_map,
        List.any_eq_true, List.mem_mapFinIdx, List.length_replicate,
        Function.comp_apply, beq_iff_eq, forall_exists_index, and_imp
      ]
      intros x1 x2 H1 H2 H3
      subst ident
      exists x1

theorem RelIO.liftFinf_get {S} {n : Nat} {i : Fin n} {f : Fin n → RelIO S}:
  (RelIO.liftFinf n f).getIO i = f i := by sorry

theorem RelIO_mapVal {α β} {n : Nat} {f : Fin n → α} {g : α → β} :
  AssocList.mapVal (λ _ => g) (RelIO.liftFinf n f) = RelIO.liftFinf n (λ i => g (f i)) :=
  by
    dsimp [RelIO.liftFinf, fin_range]
    rw [AssocList.mapVal_map_toAssocList]

-- RelInt ----------------------------------------------------------------------

@[simp] abbrev RelInt (S : Type) := S → S → Prop

def RelInt.liftFinf {S : Type} (n : Nat) (f : Fin n → List (RelInt S)) : List (RelInt S) :=
  fin_range n |>.map f |>.flatten
