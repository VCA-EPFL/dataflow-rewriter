/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import DataflowRewriter.Module
import DataflowRewriter.Component
import DataflowRewriter.Examples.Noc.Utils
import DataflowRewriter.Examples.Noc.Lang

set_option autoImplicit false
set_option linter.all false

namespace DataflowRewriter.Noc

  variable {Data : Type} [BEq Data] [LawfulBEq Data]

  @[drcomponents]
  abbrev Noc.input_rel (n : Noc Data) : n.Rel (Data × n.topology.RouterID) :=
    λ rid dir old_s val new_s =>
      -- TODO: We probably also need to say that all router other than rid are
      -- unchanged
      n.routers.input_rel rid old_s[rid] (val.1, (n.routing_pol.mkhead rid val.2 val.1)) new_s[rid]

  @[drcomponents]
  abbrev Noc.router_output_rel (n : Noc Data) :=
    λ rid dir (old_s : n.routers.State) (val : n.Flit) (new_s : n.routers.State) =>
      let val' := n.routing_pol.route rid val
      dir = val'.1 ∧
      n.routers.output_rel rid old_s val new_s

  @[drcomponents]
  abbrev Noc.output_rel (n : Noc Data) : n.Rel n.Flit :=
    λ rid dir old_s val new_s =>
      -- TODO: We probably also need to say that all router other than rid are
      -- unchanged
      n.router_output_rel rid dir old_s[rid] val new_s[rid]

  @[drcomponents]
  def Noc.mk_router_input (n : Noc Data) (rid : n.topology.RouterID) (dir : n.topology.Dir rid) : RelIO n.State :=
    ⟨
      Data × n.topology.RouterID, n.input_rel rid dir
    ⟩

  @[drcomponents]
  def Noc.mk_router_output (n : Noc Data) (rid : n.topology.RouterID) (dir : n.topology.Dir rid) : RelIO n.State :=
    ⟨
      Data,
      λ old_s out new_s => ∃ head, n.output_rel rid dir old_s (out, head) new_s
    ⟩

  @[drcomponents]
  def Noc.mk_router_conn (n : Noc Data) (rid : n.topology.RouterID) : List (RelInt n.State) :=
    (n.topology.neigh rid).mapFinIdx (λ dir rid' Hdir =>
      λ old_s new_s => ∃ val mid_s,
        n.output_rel rid (Fin.mk (dir + 1) (by simpa)) old_s val mid_s ∧
        n.routers.input_rel rid' mid_s[rid'] val new_s[rid'])

  @[drcomponents]
  def Noc.build_module (n : Noc Data) : Module Nat n.State :=
    {
      inputs := RelIO.liftFinf n.topology.netsz (λ rid => n.mk_router_input rid n.topology.DirLocal)
      outputs := RelIO.liftFinf n.topology.netsz (λ rid => n.mk_router_output rid n.topology.DirLocal)
      internals := RelInt.liftFinf n.topology.netsz n.mk_router_conn,
      init_state := λ s => s = Vector.replicate n.topology.netsz n.routers.init_state,
    }

end DataflowRewriter.Noc
