/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

-- Implementation of NoC types and reference implementation using Bags
-- Inputs are defined as a product between an arbitrary type T and a FlitHeader
-- type, which gives information about the desired target of each message.

-- FIXME: For now, there is a low of useless comments which should be removed

import Lean
import Init.Data.BitVec.Lemmas
import Qq

import DataflowRewriter.Simp
import DataflowRewriter.Module
import DataflowRewriter.ExprLow
import DataflowRewriter.Component
import DataflowRewriter.KernelRefl
import DataflowRewriter.Reduce
import DataflowRewriter.List
import DataflowRewriter.ExprHighLemmas
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

-- Types -----------------------------------------------------------------------

def RouterID : Type :=
  -- FIXME: This should be Fin T.netsz, but it is annoying
  -- Notably below for the `nbranch` component, we cannot use a List.range
  Nat

structure FlitHeader : Type :=
  dest : RouterID
-- TODO: Should this be deriving stuff ? I cannot for some reason make it work

def FlitHeaderS : String :=
  s!"FlitHeader {T.netsz}"

-- Components ------------------------------------------------------------------

@[drunfold]
def nbranch' (name := "nbranch") : NatModule (NatModule.Named name (List T.Data × List RouterID)) :=
  {
    inputs := [
      (0, ⟨T.Data,
        λ (oldDatas, oldRouterIDs) data (newDatas, newRouterIDs) =>
          newDatas = oldDatas.concat data ∧ newRouterIDs = oldRouterIDs
      ⟩),
      (1, ⟨RouterID,
        λ (oldDatas, oldRouterIDs) routerID (newDatas, newRouterIDs) =>
          newDatas = oldDatas ∧ newRouterIDs = oldRouterIDs.concat routerID
      ⟩),
    ].toAssocList

    outputs :=
      -- TODO: We would like to have n be cast to a RouterID down the line
      List.range T.netsz |>.map (λ routerID => Prod.mk ↑routerID
        (⟨T.Data,
          λ (oldDatas, oldRouterIDs) data (newDatas, newRouterIDs) =>
            data :: newDatas = oldDatas ∧
            routerID :: newRouterIDs = oldRouterIDs
        ⟩))
      |>.toAssocList,
  }

@[drunfold]
def nbranch :=
  nbranch' |>.stringify

-- Environment -----------------------------------------------------------------

def ε' : Env :=
  [
    -- Merge to implement the n-bag
    (s!"Merge {T.DataS} {T.netsz}", ⟨_, StringModule.merge T.Data T.netsz⟩),

    -- Splits to separate Data and FlitHeader
    (s!"Split {T.DataS} {FlitHeaderS}", ⟨_, StringModule.split T.Data FlitHeader⟩),

    -- Bags to receive message (One per router)
    (s!"Bag {T.DataS}", ⟨_, StringModule.bag T.Data⟩),

    -- Branching for routing
    (s!"NBranch {T.DataS} {T.netsz}", ⟨_, nbranch⟩),
  ].toAssocList

-- Implementation --------------------------------------------------------------

-- Bag with `n` inputs
def nbag (T : Type) (TS : String) (n : ℕ) : ExprHigh String :=
  {
    modules := [
      ⟨"Merge", -- Instance name
        ⟨
          {
            input :=
              List.range n |>.map (λ i =>
                ⟨
                  -- Type port (Must be inst InstIdent.top)
                  NatModule.stringify_input i,
                  -- Internal name, here a top level port
                  NatModule.stringify_input i,
                ⟩
              )
              |>.toAssocList,
            output := [⟨
                NatModule.stringify_output 0,
                -- Internal name
                {
                  -- Same Instance Name as above
                  inst := InstIdent.internal "Merge",
                  -- Arbitrary name
                  name := "merge_to_bag_out",
                }
              ⟩].toAssocList,
          },
          s!"Merge {TS} {n}" -- Instance Type
        ⟩
      ⟩,

      ⟨"Bag", -- Instance name
        ⟨
          {
            input := [
              ⟨
                NatModule.stringify_input 0,
                { inst := InstIdent.internal "Bag", name := "merge_to_bag_in" }
              ⟩
            ].toAssocList,
            output := [
              ⟨NatModule.stringify_output 0, NatModule.stringify_output 0⟩
            ].toAssocList,
          },
          s!"Bag {TS}" -- Instance Type
        ⟩
      ⟩,

    ].toAssocList,
    connections := [
      {
        output := { inst := InstIdent.internal "Merge", name := "merge_to_bag_out" },
        input := { inst := InstIdent.internal "Bag", name := "merge_to_bag_in" },
      }
    ],
  }

def nbagM :=
  [Ge| nbag T.Data T.DataS T.netsz, ε']

def ε : Env :=
  AssocList.cons
    s!"NBag {T.DataS} {T.netsz}" ⟨_, nbagM⟩ ε'

def noc : ExprHigh String :=
  {
    modules :=
      List.range T.netsz |>.map (λ i => [
        ⟨s!"Split{i}",
          ⟨
            {
              input := [
                ⟨NatModule.stringify_input 0, NatModule.stringify_input i⟩
              ].toAssocList,
              output := [
                ⟨
                  NatModule.stringify_output 0,
                  {
                    inst := InstIdent.internal s!"Split{i}",
                    name := s!"Data{i}_out"
                  }
                ⟩,
                ⟨
                  NatModule.stringify_output 1,
                  {
                    inst := InstIdent.internal s!"Split{i}",
                    name := s!"FlitHeader{i}_out"
                  }
                ⟩,
              ].toAssocList,
            },
            s!"Split {T.DataS} {FlitHeaderS}"
          ⟩
        ⟩,

        ⟨s!"NBranch{i}",
          ⟨
            {
              input := [
                ⟨
                  NatModule.stringify_input 0,
                  {
                    inst := InstIdent.internal s!"NBranch{i}",
                    name := s!"NBranch{i}_in1"
                  }
                ⟩,
                ⟨
                  NatModule.stringify_input 1,
                  {
                    inst := InstIdent.internal s!"NBranch{i}",
                    name := s!"NBranch{i}_in2"
                  }
                ⟩,
              ].toAssocList,
              output := List.range T.netsz |>.map (λ j =>
                ⟨
                  NatModule.stringify_output j,
                  {
                    inst := InstIdent.internal s!"NBranch{i}",
                    name := s!"NBranch{i}_out{j + 1}"
                  }
                ⟩
              ) |>.toAssocList
            },
            s!"NBranch {T.DataS} {T.netsz}"
          ⟩
        ⟩,

        ⟨s!"NBag{i}",
          ⟨
            {
              input := List.range T.netsz |>.map (λ j =>
                ⟨
                  NatModule.stringify_input j,
                  {
                    inst := InstIdent.internal s!"NBag{i}",
                    name := s!"NBag{i}_in{j + 1}"
                  }
                ⟩
              ) |>.toAssocList,
              output := [
                ⟨
                  NatModule.stringify_output 0,
                  NatModule.stringify_output i,
                ⟩,
              ].toAssocList,
            },
            s!"NBag {T.DataS} {T.netsz}"
          ⟩
        ⟩,
      ])
      |>.flatten
      |>.toAssocList,
    connections :=
      List.range T.netsz |>.map (λ i => ([
        {
          output :=
            {
              inst := InstIdent.internal s!"Split{i}",
              name := s!"Data{i}_out"
            }
          input :=
            {
              inst := InstIdent.internal s!"NBranch{i}",
              name := s!"Data{i}_in0"
            }
        },
        {
          output :=
            {
              inst := InstIdent.internal s!"Split{i}",
              name := s!"FlitHeader{i}_out"
            }
          input :=
            {
              inst := InstIdent.internal s!"NBranch{i}",
              name := s!"Data{i}_in1"
            }
        },
      ])
      ++
      (List.range T.netsz |>.map (λ j =>
        {
          output :=
            {
              inst := InstIdent.internal s!"NBranch{i}",
              name := s!"NBranch{i}_out{j + 1}"
            }
          input :=
            {
              inst := InstIdent.internal s!"NBag{i}",
              name := s!"NBag{i}_in{j + 1}"
            }
        }
      )))
      |>.flatten
  }

def nocM :=
  [Ge| noc, ε]

def nocT :=
  [GT| noc, ε]

-- TODO: We could prove that any RouterID has an associated input rule which is
-- unique
-- TODO: We could do the same with output rules

theorem nocM_inpT i:
  (nocM.inputs.getIO (NatModule.stringify_input i)).1 = (T.Data × FlitHeader) :=
  by
    sorry

theorem nocM_outT i:
  (nocM.outputs.getIO (NatModule.stringify_output i)).1 = (T.Data × FlitHeader) :=
    by
      sorry

-- TODO: Say that v must be ⟨j, d⟩, and so should v'
-- We prove that for every input and output, we can route a message between them
theorem full_connectivity (i j : RouterID) (d : T.Data) in_s mid_s:
  -- From any initial state `in_s`, we can reach a new state `mid_s` by using
  -- the input rule associated to `i` used with value `v`
  (nocM.inputs.getIO (NatModule.stringify_input i)).2 in_s ((nocM_inpT i).mpr (d, ⟨j⟩)) mid_s →
  ∃ out_s,
  -- There exists a path from this `mid_s` to an output state `out_s`
  existSR nocM.internals mid_s out_s ∧
  -- This `out_s` can be used to actually extract the initial value `v` in the
  (nocM.outputs.getIO (NatModule.stringify_output j)).2 mid_s ((nocM_outT j).mpr (d, ⟨j⟩)) out_s
  := by sorry

end DataflowRewriter.NoC
