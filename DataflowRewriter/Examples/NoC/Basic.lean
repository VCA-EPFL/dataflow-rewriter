/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
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

variable [T: NocParam]

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
  s!"FlitHeader {T.netsz}"

-- Component -------------------------------------------------------------------

@[drunfold]
def noc (name := "noc") : NatModule (NatModule.Named name (List (T.Data × RouterID))) :=
  {
    inputs := List.range T.netsz |>.map (λ routerID => Prod.mk ↑routerID
      ⟨
        T.Data × RouterID,
        λ oldState v newState => newState = oldState.concat v
      ⟩
    ) |>.toAssocList,
    outputs := List.range T.netsz |>.map (λ routerID => Prod.mk ↑routerID
      ⟨
        T.Data,
        λ oldState data newState => (data, routerID) :: newState = oldState
      ⟩
    ) |>.toAssocList,
  }

-- Basic properties ------------------------------------------------------------

-- TODO
-- theorem find_port {S} (i : RouterID) (f : RouterID -> ((T : Type) × (S → T → S → Prop))) k v :
--   i < T.netsz →
--   f i = ⟨ k, v ⟩ →
--   (PortMap.getIO (List.range T.netsz |>.map f |>.toAssocList) ↑i = v) := by
--     sorry

theorem noc_inpT (i : RouterID) :
  i < T.netsz → (noc.inputs.getIO ↑i).1 = (T.Data × FlitHeader) :=
  by
    unfold noc
    induction T.netsz <;> simp at *
    rename_i n H
    intros Hle
    sorry

theorem noc_outT (i : RouterID) :
  i < T.netsz →
  (noc.outputs.getIO i).1 = (T.Data × FlitHeader) :=
  by
    unfold noc
    induction T.netsz <;> simp at *
    rename_i n H
    intros Hle
    sorry

theorem full_connectivity (i j : RouterID) (d : T.Data) in_s mid_s
  (iLt : i < T.netsz) (jLt : j < T.netsz):
  -- From any initial state `in_s`, we can reach a new state `mid_s` by using
  -- the input rule associated to `i` used with value `v`
  (noc.inputs.getIO i).2 in_s ((noc_inpT i iLt).mpr (d, ⟨j⟩)) mid_s →
  ∃ out_s,
  -- There exists a path from this `mid_s` to an output state `out_s`
  existSR noc.internals mid_s out_s ∧
  -- This `out_s` can be used to actually extract the initial value `v` in the
  (noc.outputs.getIO j).2 mid_s ((noc_outT j jLt).mpr (d, ⟨j⟩)) out_s
  := by
    intros Hinp
    unfold noc at *
    dsimp at *
    exists mid_s
    split_ands
    · constructor
    · sorry

end DataflowRewriter.NoC
