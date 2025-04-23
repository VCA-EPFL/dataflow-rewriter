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

-- This definition is intuitive and it is a good example of something we would
-- like to prove correct, but unfortunately it is very hard to reduce easily,
-- most notably due the use of fold and stuff.
-- A way to improve it would be to make "routers" into it's own module type and
-- prove its correctness before using it here, but it would be very cumbersome.
-- This "router" definition would also not be a true router, as it would only
-- allow sending message to a network on its output, receiving messages on
-- inputs, but not allow communication between them, as these connections would
-- be handled by the noc.
-- The proper definition of a router is, in fact, the same definition as a noc
def noc_low : ExprLow String :=
  let empty : ExprLow String := ExprLow.base {} s!"Empty"
  let router (i : RouterID) : ExprLow String :=
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
  let connect (id_src : RouterID) (acc : ExprLow String) (id_dst : RouterID) : ExprLow String :=
      ExprLow.connect
        {
          output := {
            inst := InstIdent.internal s!"NRoute {id_src}",
            name := NatModule.stringify_output id_src
          },
          input := {
            inst := InstIdent.internal s!"NBag {id_dst}",
            name := NatModule.stringify_input id_dst
          },
        }
        acc
  List.foldl
    (λ acc i =>
      List.foldl
        (connect i)
        (ExprLow.product acc (router i))
        (List.range P.netsz)
    )
    empty
    (List.range P.netsz)

-- NOTE: This definition is much simpler and would be a lot easier to prove correct
-- and to reduce.
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
    s!"NBag {P.DataS} {P.netsz}"
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
  (ExprLow.product nbag nroute)

def noc_lowT : Type := by
  precomputeTac [T| noc_low', ε_noc] by
    simp [drunfold, seval, drdecide, -AssocList.find?_eq]
    rw [ε_noc_nbag, ε_noc_nroute]
    simp [drunfold, seval, drcompute, drdecide]

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
