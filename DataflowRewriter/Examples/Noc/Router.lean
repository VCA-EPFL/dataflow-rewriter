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

    def queue : Router netsz Flit :=
      {
        State       := List Flit
        init_state  := []
        input_rel   := λ rid flit s s' => s' = s.set rid (s[rid] ++ [flit])
        output_rel  := λ rid flit s s' => s = s'.set rid (flit :: s'[rid])
      }

    def bag : Router netsz Flit :=
      {
        State       := List Flit
        init_state  := []
        input_rel   := λ rid flit s s' => s' = s.set rid (s[rid] ++ [flit])
        output_rel  := λ rid flit s s' => ∃ i : Fin (s'[rid].length), s' = s.set rid (s'[rid].remove i)
      }

  end Unbounded

  namespace Bounded

  end Bounded

end DataflowRewriter.Noc.Router
