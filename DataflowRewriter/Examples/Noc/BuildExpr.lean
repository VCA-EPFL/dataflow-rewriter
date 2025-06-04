/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import DataflowRewriter.Module
import DataflowRewriter.Component
import DataflowRewriter.Examples.Noc.Utils
import DataflowRewriter.Examples.Noc.Lang

open Batteries (AssocList)

variable {Data : Type} [BEq Data] [LawfulBEq Data]

namespace DataflowRewriter.Noc

  @[drcomponents]
  def router_name (n : Noc Data) (rid : n.topology.RouterID) :=
    s!"Router {rid}"

  @[drcomponents]
  def router_stringify_inp (n : Noc Data) (rid : n.topology.RouterID) (dir : Nat) :=
    s!"Router {rid} in{dir}"

  @[drcomponents]
  def router_stringify_out (n : Noc Data) (rid : n.topology.RouterID) (dir : Nat) :=
    s!"Router {rid} out{dir}"

  @[drunfold_defs]
  def Noc.build_expr (n : Noc Data) : ExprLow String :=

    let router_internal (rid : n.RouterID) :=
      InstIdent.internal (router_name n rid)

    let router_out (rid : n.RouterID) (dir : n.Dir_out rid) : InternalPort String :=
      { inst := router_internal rid, name := NatModule.stringify_output dir }

    let router_inp (rid : n.RouterID) (dir : n.Dir_inp rid) : InternalPort String :=
      { inst := router_internal rid, name := NatModule.stringify_input dir }

    let mkrouter (rid : n.RouterID) : ExprLow String :=
      .base
        {
            input :=
              AssocList.cons (router_stringify_inp n rid 0) (NatModule.stringify_input rid)
                (List.map
                  (λ dir => ⟨router_stringify_inp n rid (dir + 1), router_inp rid (dir + 1)⟩)
                  (List.range (n.topology.inp_len rid))
                |>.toAssocList),
            output :=
              AssocList.cons (router_stringify_out n rid 0) (NatModule.stringify_output rid)
                (List.map
                  (λ dir => ⟨router_stringify_out n rid (dir + 1), router_out rid (dir + 1)⟩)
                  (List.range (n.topology.out_len rid))
                |>.toAssocList),
        }
        s!"Router {rid}"

    let mkrouters (acc : ExprLow String) : ExprLow String :=
      List.foldl (λ acc i => .product acc (mkrouter i)) acc (fin_range n.topology.netsz)

    let mkconns (acc : ExprLow String) : ExprLow String :=
      List.foldl
        (λ acc c  =>
          let rid_out := c.1
          let rid_inp := c.2.1
          let dir_out := c.2.2.1
          let dir_inp := c.2.2.2
          .connect
            {
              output  := router_out rid_out dir_out
              input   := router_inp rid_inp dir_inp
            }
          acc)
        acc n.topology.conns

    .base { input := .nil, output := .nil } "empty"
    |> mkrouters
    |> mkconns

end DataflowRewriter.Noc
