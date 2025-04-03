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

variable (Data : Type)    -- Type of data transmitted over the NoC
variable (DataS : String) -- String representation of Data
variable (netsz : ℕ)      -- Network Size (Number of router)

-- Types -----------------------------------------------------------------------

def RouterID (netsz : ℕ) : Type :=
  -- FIXME: This should be Fin netsz, but it is annoying
  -- Notably below for the `nbranch` component, we cannot use a List.range
  Nat

structure FlitHeader : Type :=
  dest : RouterID netsz
-- TODO: Should this be deriving stuff ? I cannot for some reason make it work

def FlitHeaderS : String :=
  s!"FlitHeader {netsz}"

-- Components ------------------------------------------------------------------

@[drunfold]
def nbranch' (name := "nbranch") : NatModule (NatModule.Named name (List Data × List (RouterID netsz))) :=
  {
    inputs := [
      (0, ⟨Data,
        λ (oldDatas, oldRouterIDs) data (newDatas, newRouterIDs) =>
          newDatas = oldDatas.concat data ∧ newRouterIDs = oldRouterIDs
      ⟩),
      (1, ⟨RouterID netsz,
        λ (oldDatas, oldRouterIDs) routerID (newDatas, newRouterIDs) =>
          newDatas = oldDatas ∧ newRouterIDs = oldRouterIDs.concat routerID
      ⟩),
    ].toAssocList

    outputs :=
      -- TODO: We would like to have n be cast to a RouterID down the line
      List.range netsz |>.map (λ routerID => Prod.mk ↑routerID
        (⟨Data,
          λ (oldDatas, oldRouterIDs) data (newDatas, newRouterIDs) =>
            data :: newDatas = oldDatas ∧
            routerID :: newRouterIDs = oldRouterIDs
        ⟩))
      |>.toAssocList,
  }

@[drunfold]
def nbranch :=
  nbranch' Data netsz |>.stringify

-- Environment -----------------------------------------------------------------

def ε' : Env :=
  [
    -- Merge to implement the n-bag
    (s!"Merge {DataS} {netsz}", ⟨_, StringModule.merge Data netsz⟩),

    -- Splits to separate Data and FlitHeader
    (s!"Split {DataS} {FlitHeaderS netsz}", ⟨_, StringModule.split Data (FlitHeader netsz)⟩),

    -- Bags to receive message (One per router)
    (s!"Bag {DataS}", ⟨_, StringModule.bag Data⟩),

    -- Branching for routing
    (s!"NBranch {DataS} {netsz}", ⟨_, nbranch Data netsz⟩),
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

def nbag_module :=
  [Ge| nbag Data DataS netsz, ε' Data DataS netsz]

def ε : Env :=
  AssocList.cons
    s!"NBag {DataS} {netsz}"
    ⟨_, nbag_module Data DataS netsz⟩
    (ε' Data DataS netsz)

def noc : ExprHigh String :=
  {
    modules :=
      List.range netsz |>.map (λ i => [
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
            s!"Split {DataS} {FlitHeaderS netsz}"
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
              output := List.range netsz |>.map (λ j =>
                ⟨
                  NatModule.stringify_output j,
                  {
                    inst := InstIdent.internal s!"NBranch{i}",
                    name := s!"NBranch{i}_out{j + 1}"
                  }
                ⟩
              ) |>.toAssocList
            },
            s!"NBranch {DataS} {netsz}"
          ⟩
        ⟩,

        ⟨s!"NBag{i}",
          ⟨
            {
              input := List.range netsz |>.map (λ j =>
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
            s!"NBag {DataS} {netsz}"
          ⟩
        ⟩,
      ])
      |>.flatten
      |>.toAssocList,
    connections :=
      List.range netsz |>.map (λ i => ([
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
      (List.range netsz |>.map (λ j =>
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
  [Ge| noc DataS netsz, ε Data DataS netsz]

def nocT :=
  [GT| noc DataS netsz, ε Data DataS netsz]

-- TODO: We could prove that any RouterID has an associated input rule which is
-- unique
-- TODO: We could do the same with output rules

-- TODO: Say that v must be ⟨j, d ⟩, and so should v'
-- We prove that for every input and output, we can route a message between them
theorem full_connectivity (i j : RouterID netsz) (d : Data) in_s in_v out_v mid_s out_s:
  -- From any initial state `in_s`, we can reach a new state `mid_s` by using
  -- the input rule associated to `i` used with value `v`
  ((nocM Data DataS netsz).inputs.getIO (NatModule.stringify_input i)).2 in_s in_v mid_s →
  -- There exists a path from this `mid_s` to an output state `out_s`
  existSR (nocM Data DataS netsz).internals mid_s out_s →
  -- This `out_s` can be used to actually extract the initial value `v` in the
  ((nocM Data DataS netsz).outputs.getIO (NatModule.stringify_input j)).2 mid_s out_v out_s
  := by sorry

end DataflowRewriter.NoC
