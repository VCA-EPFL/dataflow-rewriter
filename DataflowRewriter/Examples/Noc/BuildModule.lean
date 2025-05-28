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
  def Noc.output_rel (n : Noc Data) (rid : n.topology.RouterID) (dir : n.topology.Dir rid) (val : n.routing_pol.Flit) (old_s new_s : n.routers.NocState) : Prop :=
      let val' := n.routing_pol.route rid val
      dir = val'.1 ∧ n.routers.output_rel rid val'.2 old_s new_s

  @[drcomponents]
  def Noc.mk_router_input (n : Noc Data) (rid : n.topology.RouterID) : RelIO n.routers.NocState :=
    ⟨
      Data × n.topology.RouterID,
      λ old_s inp new_s =>
        n.routers.input_rel rid (inp.1, (n.routing_pol.mkhead rid inp.2 inp.1)) old_s new_s
    ⟩

  @[drcomponents]
  def Noc.mk_router_output (n : Noc Data) (rid : n.topology.RouterID) (dir : n.topology.Dir rid) : RelIO n.routers.NocState :=
    ⟨
      Data,
      λ old_s out new_s => ∃ head,
        n.output_rel rid dir (out, head) old_s new_s
    ⟩

  @[drcomponents]
  def Noc.mk_router_conn (n : Noc Data) (rid : n.topology.RouterID) : List (RelInt n.routers.NocState) :=
    (n.topology.neigh rid).mapFinIdx (λ dir rid' Hdir =>
      λ old_s new_s => ∃ val mid_s,
        n.output_rel rid (Fin.mk (dir + 1) (by simpa)) val old_s mid_s ∧
        n.routers.input_rel rid' val mid_s new_s)

  @[drcomponents]
  def Noc.build_module (n : Noc Data) : Module Nat n.routers.NocState :=
    {
      inputs := RelIO.liftFinf n.topology.netsz n.mk_router_input
      outputs := RelIO.liftFinf n.topology.netsz (λ rid => n.mk_router_output rid n.topology.DirLocal)
      internals := RelInt.liftFinf n.topology.netsz n.mk_router_conn,
      init_state := λ s => s = Vector.replicate n.topology.netsz n.routers.init_state,
    }

end DataflowRewriter.Noc
