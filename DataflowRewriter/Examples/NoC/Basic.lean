/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

-- Implementation of NoC types and reference implementation using Bags
-- Inputs are defined as a product between an arbitrary type T and a FlitHeader
-- type, which gives information about the desired target of each message.

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

open Batteries (AssocList)

namespace DataflowRewriter.NoC

-- Parameters ------------------------------------------------------------------

-- TODO: Maybe a comment here to explain Yann's hack would be great since this
-- is also an Example file
class NocParam where
  Data : Type     -- Type of data transmitted over the NoC
  DataS : String  -- String representation of Data
  netsz : Nat     -- Network Size (Number of router)

variable [P: NocParam]

-- TODO: Unsure why this needs to be an abbrev
abbrev RouterID :=
  -- FIXME: This could be a Fin T.netsz, should it ?
  -- What is the expected behavior of a NoC in which the target is invalid?
  -- Making this a Fin T.netsz makes the below design harder, since we cannot
  -- range over Fin
  Nat

structure FlitHeader : Type :=
  dest : RouterID

def FlitHeaderS : String :=
  s!"FlitHeader {P.netsz}"

-- Component -------------------------------------------------------------------

def nocT : Type :=
  List (P.Data × FlitHeader)

def mk_input_rule (rID : RouterID) : (InternalPort Nat × (Σ T : Type, nocT → T → nocT → Prop)) :=
  Prod.mk ↑rID ⟨P.Data × FlitHeader, λ oldState v newState => newState = oldState.concat v ⟩

def mk_output_rule (rID : RouterID) : (InternalPort Nat × (Σ T : Type, nocT → T → nocT → Prop)) :=
  Prod.mk ↑rID
    ⟨
      P.Data,
      λ oldState data newState => (data, { dest := rID }) :: newState = oldState
    ⟩

@[drunfold]
def noc (name := "noc") : NatModule (NatModule.Named name nocT) :=
  {
    inputs := List.range P.netsz |>.map mk_input_rule |>.toAssocList,
    outputs := List.range P.netsz |>.map mk_output_rule |>.toAssocList,
  }

-- Basic properties ------------------------------------------------------------

theorem noc_inpT (i : RouterID) :
  i < P.netsz → (noc.inputs.getIO ↑i).1 = (P.Data × FlitHeader) :=
  by
    unfold noc
    dsimp
    intros Hle
    rw [PortMap.getIO_map (sz := P.netsz) (i := i) (f := mk_input_rule)]
    rotate_left 4
    · unfold mk_input_rule; rfl
    · simpa
    · simpa

theorem noc_outT (i : RouterID) :
  i < P.netsz →
  (noc.outputs.getIO i).1 = P.Data :=
  by
    unfold noc
    dsimp
    intros Hle
    rw [PortMap.getIO_map (sz := P.netsz) (i := i) (f := mk_output_rule)]
    rotate_left 4
    · unfold mk_output_rule; rfl
    · simpa
    · simpa

theorem full_connectivity (i j : RouterID) (d : P.Data) in_s mid_s
  (iLt : i < P.netsz) (jLt : j < P.netsz):
  -- From any initial state `in_s`, we can reach a new state `mid_s` by using
  -- the input rule associated to `i` used with value `v`
  (noc.inputs.getIO i).2 in_s ((noc_inpT i iLt).mpr (d, ⟨j⟩)) mid_s →
  ∃ out_s,
  -- There exists a path from this `mid_s` to an output state `out_s`
  -- TODO: Here, we know for sure that noc.internals is empty, since we just
  -- defined it that way.
  -- Does it then still really make sense to express it this way?
  existSR noc.internals mid_s out_s ∧
  -- This `out_s` can be used to actually extract the initial value `v` in the
  (noc.outputs.getIO j).2 mid_s ((noc_outT j jLt).mpr d) out_s
  := by
    intros Hinp
    unfold noc at *
    dsimp at *
    exists mid_s
    split_ands
    · constructor
    · -- TODO(Ask Yann): Why don't I get this definition as hypothesis ?
      -- How can I get it?
      let (kinp, vinp) := mk_input_rule i
      -- TODO(Ask Yann): Is there a cleaner way to do this...
      rw [PortMap.rw_rule_execution (h := PortMap.getIO_map (sz := P.netsz) (i := i) (f := mk_input_rule) kinp vinp iLt _)] at Hinp
      · simp at *
        let (kout, vout) := mk_output_rule i
        rw [PortMap.rw_rule_execution (h := PortMap.getIO_map (sz := P.netsz) (i := j) (f := mk_output_rule) kout vout jLt _)]
        · sorry
        · sorry
      · sorry

end DataflowRewriter.NoC
