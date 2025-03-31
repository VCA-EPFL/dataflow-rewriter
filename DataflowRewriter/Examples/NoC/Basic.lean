-- Implementation of NoC types and reference implementation using Bags
-- Inputs are defined as a product between an arbitrary type T and a FlitHeader
-- type, which gives information about the desired target of each message.

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

def RouterID : Type :=
  Fin netsz

structure FlitHeader : Type :=
  dest: RouterID netsz
-- TODO: Should this be deriving other stuff ?

def Ident : Type :=
  String

-- Environment -----------------------------------------------------------------

def ε : IdentMap Ident (TModule1 Ident) :=
  [
    (s!"Merge {netsz}", ⟨_, StringModule.merge Data netsz⟩),
    -- TODO: Should we add Data and FlitHeader to Split Name ?
    ("Split",           ⟨_, StringModule.split Data (FlitHeader netsz)⟩),
    ("Bag",             ⟨_, StringModule.bag Data⟩),

    -- TODO: We actually need a Mux of nsz input, how could we get this?
    -- Do we have to make it ourself?
  ].toAssocList

-- Implementation --------------------------------------------------------------

-- TODO: Define a nbag component by using a n-merge into a bag
def nbag : ExprHigh Ident :=
  { modules := [].toAssocList, connections := [] }

-- TODO: Define a nmux component

-- TODO: Define a NoC using nmux, nbag, split, merge, ...
-- Should the FlitHeader part be part of the received data?

end DataflowRewriter.NoC
