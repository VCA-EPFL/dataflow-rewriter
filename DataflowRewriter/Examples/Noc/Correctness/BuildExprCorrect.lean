/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import DataflowRewriter.Module
import DataflowRewriter.ModuleLemmas
import DataflowRewriter.Component
import DataflowRewriter.Examples.Noc.Utils
import DataflowRewriter.Examples.Noc.Lang
import DataflowRewriter.Examples.Noc.Spec
import DataflowRewriter.Examples.Noc.BuildExpr

open Batteries (AssocList)

variable {Data : Type} [BEq Data] [LawfulBEq Data]

namespace DataflowRewriter.Noc

  -- We need an environment correctness property:
  --  · Each router is in the env, with correct amount of input/output
  --  · Each router implementation respect the specification given for a router
  def Noc.env_correct (n : Noc Data) (ε : Env) : Prop :=
    ∀ rid : n.topology.RouterID, ∃ rmod,
      AssocList.find? (router_name n rid) ε = .some rmod
      ∧ rmod.2 ⊑ (n.spec_router rid)
      -- TODO: On top of every router is in the module, we also need to have
      -- rmod ⊑ n.rspec rid (The spec should be fairly straightforward to get)

end DataflowRewriter.Noc
