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

variable (Data : Type)  -- Type of data transmitted over the NoC
variable (netsz : ℕ)    -- Network Size (Number of router)

-- Types -----------------------------------------------------------------------

def RouterID (netsz : ℕ) : Type :=
  -- FIXME: Fin netsz could be better, but it is annoying to use.
  -- Notably below for the `nbranch` component,
  -- we cannot easily use a List.range.
  Nat

structure FlitHeader : Type :=
  dest: RouterID netsz
-- TODO: Should this be deriving stuff ?

def Ident : Type :=
  String

-- Components ------------------------------------------------------------------

-- TODO: Do we need to have netsz in name ?
@[drunfold]
def nbranch' (name := "nbranch") : NatModule (List Data × List (RouterID netsz)) :=
  { inputs :=
    [
      (0, ⟨
        Data,
        λ (oldValList, oldRouterIDList) val (newValList, newRouterIDList) =>
          newValList = oldValList.concat val ∧ newRouterIDList = oldRouterIDList
      ⟩),
      (1, ⟨
        RouterID netsz,
        λ (oldValList, oldRouterIDList) b (newValList, newRouterIDList) =>
          newValList = oldValList ∧ newRouterIDList = oldRouterIDList.concat b
      ⟩),
    ].toAssocList
    outputs :=
    -- TODO: We would like to have n be cast to a RouterID down the line
      List.range netsz |>.map (λ n => Prod.mk ↑n
        (⟨
          Data,
          λ (oldValList, oldRouterIDList) val (newValList, newRouterIDList) =>
            val :: newValList = oldValList ∧
            n :: newRouterIDList = oldRouterIDList
        ⟩))
      |>.toAssocList,
  }

@[drunfold]
def nbranch :=
  nbranch' Data netsz |>.stringify

-- Environment -----------------------------------------------------------------

def ε : IdentMap Ident (TModule1 Ident) :=
  [
    -- TODO: Do we really require a merge ? Why would we ?
    -- Merge might be necessary if we want to also give the FlitHeader to the
    -- output flit ? Might make things harder for no reason, target shouldn't
    -- care about header
    (s!"Merge {netsz}", ⟨_, StringModule.merge Data netsz⟩),

    -- Splits are used to separate Data and FlitHeader
    -- TODO: Should we add Data and FlitHeader to Split Name ?
    ("Split",           ⟨_, StringModule.split Data (FlitHeader netsz)⟩),

    -- Bags are used to receive message (One per router)
    ("Bag",             ⟨_, StringModule.bag Data⟩),

    -- Branching is used for routing
    ("NBranch",         ⟨_, nbranch Data netsz⟩),
  ].toAssocList

-- Implementation --------------------------------------------------------------

-- TODO: Define a nbag component by using a n-merge into a bag
def nbag : ExprHigh Ident :=
  { modules := [].toAssocList, connections := [] }

-- TODO: Define a NoC using, for each input, a split into a nbranch into each
-- nbag

def noc : ExprHigh Ident :=
  { modules := [].toAssocList, connections := [] }

end DataflowRewriter.NoC
