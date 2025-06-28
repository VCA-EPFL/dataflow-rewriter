/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

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
import DataflowRewriter.ExprHigh

open Batteries (AssocList)

namespace DataflowRewriter

@[drunfold] def merge T : StringModule (List T) :=
      { inputs := [(⟨.top, "in2"⟩, ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩),
                   (⟨.top, "in3"⟩, ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩)].toAssocList,
        outputs := [(⟨.top, "out"⟩, ⟨ T, λ oldList oldElement newList =>
                           ∃ i, newList = oldList.remove i
                             ∧ oldElement = oldList.get i ⟩)].toAssocList,
        internals := []
      }

@[drunfold] def fork T : StringModule (List T) :=
      { inputs := [(⟨.top, "inp"⟩, ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩)].toAssocList,
        outputs := [ (⟨.top, "out2"⟩, ⟨ T, λ oldList oldElement newList => ∃ i, newList = oldList.remove i ∧ oldElement = oldList.get i ⟩)
                   , (⟨.top, "out3"⟩, ⟨ T, λ oldList oldElement newList => ∃ i, newList = oldList.remove i ∧ oldElement = oldList.get i ⟩)
                   ].toAssocList,
        internals := []
      }

def threemerge T : StringModule (List T):=
  { inputs := [(⟨.top, "in2"⟩, ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩),
               (⟨.top, "in3"⟩, ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩),
               (⟨.top, "in4"⟩, ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩)].toAssocList,
    outputs := [(⟨.top, "out"⟩, ⟨ T, λ oldList oldElement newList => ∃ i, newList = oldList.remove i ∧ oldElement = oldList.get i ⟩)].toAssocList,
    internals := []
  }

def ε : IdentMap String ((T : Type _) × Module String T) := [("fork", ⟨ List Nat, fork Nat ⟩), ("merge", ⟨ List Nat, merge Nat ⟩), ("merge3", ⟨ List Nat, threemerge Nat ⟩)].toAssocList

def circuit : ExprHigh String :=
  [graph|
    src0 [mod="io"];
    snk0 [mod="io"];

    fork1 [mod="fork"];
    fork2 [mod="fork"];
    merge1 [mod="merge"];
    merge2 [mod="merge"];

    src0 -> fork1 [inp="inp", out="inp"];

    fork1 -> fork2 [out="out2",inp="inp"];

    fork1 -> merge1 [out="out3",inp="in2"];
    fork2 -> merge1 [out="out2",inp="in3"];
    fork2 -> merge2 [out="out3",inp="in2"];

    merge1 -> merge2 [out="out",inp="in3"];

    merge2 -> snk0 [out="out", inp="out"];
  ]

#reduce circuit.lower
#reallyReduce circuit.build_module ε

def partition := circuit.partition ["merge1", "merge2"]
  [("in2", ⟨.internal "merge1", "in2"⟩), ("in3", ⟨.internal "merge1", "in3"⟩), ("in4", ⟨.internal "merge2", "in2"⟩)].toAssocList
  [].toAssocList

#eval partition

#reallyReduce partition.snd.build_module ε

#reduce partition.fst

def partition' := partition.fst.abstract'' "imerge3" "merge3" ["in2", "in3", "in4"] ["out"]
def partition'' := partition.fst.inlineD ((threemerge Nat).liftGraph "imerge3" "merge3")

#reduce ((threemerge Nat).liftGraph "imerge3" "merge3")

#eval partition''

/- generated from threemerge -/

-- def threemerge_int T : StringModule (List T) :=
--   { inputs := [(⟨.internal "merge1", "in2"⟩, ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩),
--                (⟨.internal "merge1", "in3"⟩, ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩),
--                (⟨.internal "merge2", "in3"⟩, ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩)].toAssocList,
--     outputs := [(⟨.internal "merge2", "out"⟩, ⟨ T, λ oldList oldElement newList => ∃ i, newList = oldList.remove i ∧ oldElement = oldList.get i ⟩)].toAssocList,
--     internals := []
--   }

end DataflowRewriter
