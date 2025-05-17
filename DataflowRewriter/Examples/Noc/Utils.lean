/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

-- A bunch of random stuff which does'nt quite fit with the rest

import DataflowRewriter.Module
import DataflowRewriter.Component

namespace DataflowRewriter.Noc

@[simp] abbrev RelInt (S : Type) :=
  S → S → Prop

@[simp] abbrev RelIO (S : Type) :=
  Σ T : Type, S → T → S → Prop

@[drcomponents]
def fin_range (sz : Nat) : List (Fin sz) :=
  List.replicate sz 0
  |>.mapFinIdx (λ i _ h => Fin.mk i (by rwa [List.length_replicate] at h))

@[drcomponents]
def RelIO.liftFinf {S : Type} (n : Nat) (f : Fin n → RelIO S) : PortMap Nat (RelIO S) :=
  fin_range n |>.map (λ i => ⟨↑i.toNat, f i⟩) |>.toAssocList

@[drcomponents]
def RelInt.liftFinf {S : Type} (n : Nat) (f : Fin n → List (RelInt S)) : List (RelInt S) :=
  fin_range n |>.map f |>.flatten
