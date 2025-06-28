/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import DataflowRewriter.Module
import DataflowRewriter.ModuleLemmas
import DataflowRewriter.Component
import DataflowRewriter.Examples.Noc.Lang

namespace DataflowRewriter.Noc.Router

  variable (netsz : Netsz) (Flit : Type)

  namespace Unbounded

    @[drunfold_defs]
    def queue : Router netsz Flit :=
      {
        State       := List Flit
        init_state  := []
        input_rel   := λ rid s flit s' => s' = s ++ [flit]
        output_rel  := λ rid s flit s' => s = flit :: s'
      }

    @[drunfold_defs]
    def bag : Router netsz Flit :=
      {
        State       := List Flit
        init_state  := []
        input_rel   := λ rid s flit s' => s' = s ++ [flit]
        output_rel  := λ rid s flit s' => ∃ i : Fin (s.length), s' = s.remove i
      }

  end Unbounded

  namespace Bounded

    variable (len : Nat)

    @[drunfold_defs]
    def queue : Router netsz Flit :=
      {
        State       := List Flit
        init_state  := []
        input_rel   := λ rid s flit s' => s'.length < len ∧ s' = s ++ [flit]
        output_rel  := λ rid s flit s' => s = flit :: s'
      }

    @[drunfold_defs]
    def bag : Router netsz Flit :=
      {
        State       := List Flit
        init_state  := []
        input_rel   := λ rid s flit s' => s'.length < len ∧ s' = s ++ [flit]
        output_rel  := λ rid s flit s' => ∃ i : Fin (s.length), s' = s.remove i
      }

  end Bounded

end DataflowRewriter.Noc.Router
