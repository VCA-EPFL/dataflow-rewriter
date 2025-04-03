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
  -- FIXME: Fin netsz could be better, but it is annoying to use.
  -- Notably below for the `nbranch` component,
  -- we cannot easily use a List.range.
  Nat

structure FlitHeader : Type :=
  dest: RouterID netsz
-- TODO: Should this be deriving stuff ? I cannot for some reason make it work

def FlitHeaderS : String :=
  s!"FlitHeader {netsz}"

-- Components ------------------------------------------------------------------

-- TODO: Do we need to have netsz in name ?
-- TODO: Maybe this could replace the current global branch definition ?
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

def ε' : IdentMap String (TModule1 String) :=
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
              (⟨
                NatModule.stringify_input i, -- Type port (Must be inst InstIdent.top)
                NatModule.stringify_input i, -- Internal name
              ⟩))
              |>.toAssocList,
            output := [
              ⟨
                NatModule.stringify_output 0,
                {
                  inst := InstIdent.internal "Merge", -- Same Instance Name as above
                  name := "merge_to_bag_out", -- Arbitrary name
                }
              ⟩
            ].toAssocList,
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

-- TODO: Define the final ε which is ε' extended with nbag

def noc : ExprHigh String :=
  {
    modules :=
      List.range netsz |>.map (λ i => [
        -- TODO: For each router:
        --  · 1 split
        --  · 1 nbranch
        --  · 1 nbag:
        --    TODO: How can I actually have this ? Its an exprHigh, do I
        --    have to compile it and then add it to the environment?
        ⟨s!"Split{i}", -- Instance name
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
            s!"Split {DataS} {FlitHeaderS netsz}" -- Instance Type
          ⟩
        ⟩,

        ⟨s!"NBranch{i}", -- Instance name
          ⟨
            {
              input := [
                ⟨
                  NatModule.stringify_input 0,
                  -- TODO: This should be an internal name
                  s!"NBranch{i}_in0"
                ⟩,
                ⟨
                  NatModule.stringify_input 1,
                  -- TODO: This should be an internal name
                  s!"NBranch{i}_in1"
                ⟩,
              ].toAssocList,
              output := List.range netsz |>.map (λ j =>
                ⟨
                  NatModule.stringify_output j,
                  -- TODO: This should be an internal name
                  s!"NBranch{i}_out{j}"
                ⟩
              ) |>.toAssocList
            },
            s!"NBranch {DataS} {netsz}" -- Instance Type
          ⟩
        ⟩,
        -- TODO: nbag: Need to be added to the environment
      ])
      |>.flatten
      |>.toAssocList,
    connections :=
      List.range netsz |>.map (λ i => [
        -- TODO: For each router:
        --  · connect global inputs to split
        --  · connect split to nbranch
        --  · connect nbranch to other nbag
        --  · connect nbag to global output
      ])
      |>.flatten
  }

-- TODO: Do we have some lemmas which we would like to prove on this
-- specification of NoC?

-- Prove full connectivity: For every input and output, we can route between
-- them

end DataflowRewriter.NoC
