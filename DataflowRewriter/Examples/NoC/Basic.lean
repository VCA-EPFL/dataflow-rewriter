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
      (0, ⟨
        Data,
        λ (oldDatas, oldRouterIDs) data (newDatas, newRouterIDs) =>
          newDatas = oldDatas.concat data ∧ newRouterIDs = oldRouterIDs
      ⟩),
      (1, ⟨
        RouterID netsz,
        λ (oldDatas, oldRouterIDs) routerID (newDatas, newRouterIDs) =>
          newDatas = oldDatas ∧ newRouterIDs = oldRouterIDs.concat routerID
      ⟩),
    ].toAssocList

    outputs :=
      -- TODO: We would like to have n be cast to a RouterID down the line
      List.range netsz |>.map (λ routerID => Prod.mk ↑routerID
        (⟨
          Data,
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

def ε : IdentMap String (TModule1 String) :=
  [
    -- TODO: Do we really require a merge ? Why would we ?
    -- Merge might be necessary if we want to also give the FlitHeader to the
    -- output flit ? Might make things harder for no reason, target shouldn't
    -- care about header
    (s!"Merge {DataS} {netsz}", ⟨_, StringModule.merge Data netsz⟩),

    -- Splits are used to separate Data and FlitHeader
    -- TODO: Should we add Data and FlitHeader to Split Name ?
    (s!"Split {DataS} {FlitHeaderS netsz}", ⟨_, StringModule.split Data (FlitHeader netsz)⟩),

    -- Bags are used to receive message (One per router)
    (s!"Bag {DataS}", ⟨_, StringModule.bag Data⟩),

    -- Branching is used for routing
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
                -- FIXME: Is this ok to be the same as name below ?
                s!"in{i + 1}", -- Type port (Must be inst InstIdent.top)
                {
                  inst := InstIdent.top
                  -- FIXME: This feels a bit weak, we are relying on the
                  -- implementation of NatModule.stringify
                  name := s!"in{i + 1}"
                } -- Internal name
              ⟩))
              |>.toAssocList,
            output := [
              ⟨
                "merge_to_bag_out",
                {
                  -- FIXME: What should be here ? top or internal ?
                  inst := InstIdent.internal "",
                  -- FIXME: This feels a bit weak, we are relying on the
                  -- implementation of NatModule.stringify
                  name := "out0",
                }
              ⟩
            ].toAssocList,
          },
          s!"Merge {TS} {n}" -- Instance Type
        ⟩
      ⟩,

      ⟨
        "Bag", -- Instance name
        ⟨
          {
            input := [
              ⟨
                "merge_to_bag_in",
                  -- FIXME: What should be here ? top or internal ?
                { inst := InstIdent.top, name := "in0" }
              ⟩
            ].toAssocList,
            output := [
              ⟨"out0", { inst := InstIdent.top, name := "out0" }⟩
            ].toAssocList,
          },
          s!"Bag {TS}" -- Instance Type
        ⟩
      ⟩,

      -- TODO: n-merge component
      -- TODO: bag component
      -- Do we need IO components ? A bit unclear
    ].toAssocList,
    connections := [
      {
        -- FIXME: I'm not sure I understand why this is an InternalPort ?
        input := { inst := InstIdent.top, name := "merge_to_bag_in" },
        -- FIXME: I'm not sure I understand why this is an InternalPort ?
        output := { inst := InstIdent.top, name := "merge_to_bag_out" },
      }
    ],
  }

def nbag_module :=
  [Ge| nbag Data DataS netsz, ε Data DataS netsz]

#reduce (types := true) (nbag_module Data DataS netsz)

-- TODO: Define a NoC using, for each input, a split into a nbranch into each
-- nbag
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
        ⟨
          s!"Split{i}", -- Instance name
          ⟨
            {
              input := [⟨"in0", s!"in{i}"⟩].toAssocList,
              output := [
                ⟨s!"split_{i}_out0", { inst := InstIdent.top, name := "out0" }⟩,
                ⟨s!"split_{i}_out1", { inst := InstIdent.top, name := "out1" }⟩,
              ].toAssocList,
            },
            s!"Split {DataS} {FlitHeaderS netsz}" -- Instance Type
          ⟩
        ⟩,

        ⟨
          s!"NBranch{i}", -- Instance name
          ⟨
            {
              input := [
                ⟨s!"NBranch{i}_in0", { inst := InstIdent.top, name := "in0" }⟩,
                ⟨s!"NBranch{i}_in1", { inst := InstIdent.top, name := "in1" }⟩,
              ].toAssocList,
              output := List.range netsz |>.map (λ j =>
                ⟨s!"NBranch{i}_out{j}", { inst := InstIdent.top, name := "out{j}" }⟩
              ) |>.toAssocList
            },
            s!"NBranch {DataS} {netsz}" -- Instance Type
          ⟩
        ⟩,
        -- TODO: nbag. How to actually use it? Its an ExprHigh, not a component
        -- Do I have to compile it and then add it to the environment?
        -- -> Yes
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
