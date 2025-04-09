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
import DataflowRewriter.Component
import DataflowRewriter.KernelRefl
import DataflowRewriter.Reduce
import DataflowRewriter.List
import DataflowRewriter.Tactic
import DataflowRewriter.AssocList
import DataflowRewriter.Examples.NoC.Basic
import DataflowRewriter.Examples.NoC.Components

open Batteries (AssocList)

namespace DataflowRewriter.NoC

variable [P: NocParam]

-- Implementation --------------------------------------------------------------

-- Bag with `n` inputs
-- TODO: We should be able to reason about this design inductively but it may be
-- very hard since n is a direct parameter of the merge
-- Another possibility would be to not use a nmerge but only use `two merge`
-- combined in cascade
def nbag (T : Type) (TS : String) (n : ℕ) : ExprLow String :=
  let merge := ExprLow.base
    {
      input := List.range n |>.map (λ i => ⟨
        -- Type port (Must be inst InstIdent.top)
        NatModule.stringify_input i,
        -- Internal name, here a top level port
        NatModule.stringify_input i,
      ⟩) |>.toAssocList,
      output := [⟨
          -- Type port (Must be inst InstIdent.top)
          NatModule.stringify_output 0,
          -- Internal name
          { inst := InstIdent.internal "Merge", name := "merge_to_bag_out" }
      ⟩].toAssocList,
    }
    s!"Merge {TS} {n}" -- Instance Type
  let bag := ExprLow.base
    {
      input := [⟨
        NatModule.stringify_input 0,
        { inst := InstIdent.internal "Bag", name := "merge_to_bag_in" }
      ⟩].toAssocList,
      output := [⟨
        NatModule.stringify_output 0,
        NatModule.stringify_output 0
      ⟩].toAssocList,
    }
    s!"Bag {TS}" -- Instance Type
  ExprLow.connect
    {
      output  := { inst := InstIdent.internal "Merge",  name := "merge_to_bag_out"  },
      input   := { inst := InstIdent.internal "Bag",    name := "merge_to_bag_in"   },
    }
    (ExprLow.product bag merge)

def nbagT :=
  [T| nbag P.Data P.DataS P.netsz, ε']

def nbagM :=
  [e| nbag P.Data P.DataS P.netsz, ε']

def nbagT_precompute : Type := by
  precomputeTac nbagT by
    unfold nbagT
    simp [drunfold,seval,drdecide,-AssocList.find?_eq]
    rw [ε'_merge,ε'_bag]
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq]

-- This should be spit out automatically
axiom nbagT_eq : nbagT = nbagT_precompute

def nbagM_precompute : StringModule nbagT_precompute := by
  precomputeTac nbagM by
    simp [drunfold,seval,drdecide,-AssocList.find?_eq]
    unfold nbagM nbag
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq]
    rw [ε'_merge,ε'_bag]
    dsimp
    -- rw [AssocList.find?_gss]
    conv =>
      pattern (occs := *) Module.connect'' _ _
      all_goals
        rw [(Module.connect''_dep_rw (h := by simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?]; rfl)
                                     (h' := by simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?]; rfl))]; rfl
    -- simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,-Prod.exists]
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?,AssocList.filter,-Prod.exists]
    unfold Module.connect''
    simp

end DataflowRewriter.NoC
