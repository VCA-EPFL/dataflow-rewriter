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

import DataflowRewriter.Examples.NoC.Basic
import DataflowRewriter.Examples.NoC.BasicLemmas
import DataflowRewriter.Examples.NoC.Components

open Batteries (AssocList)

namespace DataflowRewriter.NoC

variable [P : NocParam]

attribute [drcompute] Batteries.AssocList.toList Function.uncurry Module.mapIdent
  List.toAssocList List.foldl Option.pure_def Option.bind_eq_bind Option.bind_some
  Module.renamePorts Batteries.AssocList.mapKey InternalPort.map Nat.repr
  Nat.toDigits Nat.toDigitsCore Nat.digitChar List.asString Option.bind
  Batteries.AssocList.mapVal beq_self_eq_true
  Option.getD cond beq_self_eq_true beq_iff_eq  InternalPort.mk.injEq
  String.reduceEq and_false imp_self BEq.beq AssocList.bijectivePortRenaming
  AssocList.keysList List.inter AssocList.filterId
  AssocList.append AssocList.filter

attribute [drdecide] InternalPort.mk.injEq and_false decide_False decide_True
  and_true Batteries.AssocList.eraseAllP  InternalPort.mk.injEq
  and_false decide_False decide_True reduceCtorEq cond List.map List.elem_eq_mem
  List.mem_cons List.mem_singleton Bool.decide_or InternalPort.mk.injEq
  String.reduceEq and_false decide_false reduceCtorEq and_self Bool.or_self
  Bool.false_eq_true not_false_eq_true List.filter_cons_of_neg and_true
  List.filter_nil List.empty_eq decide_true List.nodup_cons List.not_mem_nil
  List.nodup_nil Bool.and_self reduceIte List.concat_eq_append dreduceIte
  List.append_nil

-- Implementation --------------------------------------------------------------

def ε_noc : Env :=
  [
    -- Empty component (Always useful)
    (s!"Empty", ⟨_, StringModule.empty⟩),

    -- Bags to receive message (One per router)
    (s!"NBag {P.DataS} {P.netsz}", ⟨_, StringModule.bag P.Data⟩),

    -- Branching for routing
    (s!"NRoute {P.DataS} {P.netsz}", ⟨_, nbranch⟩),
  ].toAssocList

def ε_noc_empty :
  ε_noc.find? s!"Empty" = .some ⟨_, StringModule.empty⟩ := by
  simpa

def ε_noc_nroute :
  ε_noc.find? s!"NRoute {P.DataS} {P.netsz}" = .some ⟨_, nroute⟩ := by sorry

def ε_noc_nbag :
  ε_noc.find? s!"NBag {P.DataS} {P.netsz}" = .some ⟨_, nbag P.Data P.netsz⟩ := by sorry

def noc_low : ExprLow String :=
  let empty : ExprLow String := ExprLow.base {} s!"Empty"
  let gadget (i : RouterID) : ExprLow String :=
    let nroute := ExprLow.base
      {
        input := [⟨
          NatModule.stringify_input 0,
          NatModule.stringify_input i,
        ⟩].toAssocList,
        output := List.range P.netsz |>.map (λ j => ⟨
          NatModule.stringify_output j,
          { inst := InstIdent.internal s!"NRoute {i}", name := NatModule.stringify_output j}
        ⟩) |>.toAssocList
      }
      s!"NRoute {P.DataS} {P.netsz}"
    let nbag : ExprLow String := ExprLow.base
      {
        input := List.range P.netsz |>.map (λ j => ⟨
          NatModule.stringify_input j,
          { inst := InstIdent.internal s!"NBag {i}", name := NatModule.stringify_input j }
        ⟩) |>.toAssocList,
        output := [⟨
          NatModule.stringify_output 0,
          NatModule.stringify_output i
        ⟩].toAssocList,
      }
      s!"NBag {P.DataS} {P.netsz}"
    ExprLow.product nbag nroute
  List.foldl (fun acc i =>
    List.foldl (fun acc j =>
      ExprLow.connect
      {
        output := { inst := InstIdent.internal s!"NRoute {i}", name := NatModule.stringify_output i },
        input := { inst := InstIdent.internal s!"NBag {i}", name := NatModule.stringify_input i },
      }
      acc
    )
    (ExprLow.product acc (gadget i))
    (List.range P.netsz)
  )
  empty
  (List.range P.netsz)

def noc_lowT : Type := by
  precomputeTac [T| noc_low, ε_noc] by
    unfold noc_low
    -- TODO

def noc_lowM : StringModule noc_lowT := by
  precomputeTac [e| noc_low, ε_noc] by
    unfold noc_low
    -- TODO

-- Correctness -----------------------------------------------------------------
-- TODO

instance : MatchInterface noc_lowM noc where
  input_types := by sorry
  output_types := by sorry
  inputs_present := by sorry
  outputs_present := by sorry

def φ (I : noc_lowT) (S : nocT) : Prop :=
  False

theorem noc_low_refines_initial :
  Module.refines_initial noc_lowM noc φ := by
    sorry

theorem noc_low_refines_φ : noc_lowM ⊑_{φ} noc := by
  sorry

theorem noc_low_ϕ_indistinguishable :
  ∀ x y, φ x y → Module.indistinguishable noc_lowM noc x y := by
    sorry

theorem noc_low_correct : noc_lowM ⊑ noc := by
  apply (
    Module.refines_φ_refines
    noc_low_ϕ_indistinguishable
    noc_low_refines_initial
    noc_low_refines_φ
  )

end DataflowRewriter.NoC
