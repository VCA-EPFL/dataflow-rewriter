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

    let mkconn (acc : ExprLow String) (rid : n.RouterID) : ExprLow String :=
      AssocList.foldl
        (λ acc dir_out inp =>
          .connect
            {
              output  := router_out rid dir_out
              input   := router_inp inp.1 inp.2
            }
          acc)
        acc (n.topology.conn rid)

    let mkconns (acc : ExprLow String) : ExprLow String :=
      List.foldl mkconn acc (fin_range n.topology.netsz)

    .base { input := .nil, output := .nil } "empty"
    |> mkrouters

end DataflowRewriter.Noc
