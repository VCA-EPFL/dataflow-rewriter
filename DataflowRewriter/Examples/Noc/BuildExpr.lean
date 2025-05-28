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
  def router_stringify_inp (n : Noc Data) (rid : n.topology.RouterID) (dir : n.topology.Dir rid) :=
    s!"Router {rid} in{dir}"

  @[drcomponents]
  def router_stringify_out (n : Noc Data) (rid : n.topology.RouterID) (dir : n.topology.Dir rid) :=
    s!"Router {rid} out{dir}"

  @[drcomponents]
  def Noc.build_expr (n : Noc Data) : ExprLow String :=

    let RouterID :=
      n.topology.RouterID

    let Dir (rid : RouterID) :=
      n.topology.Dir rid

    let router_internal (rid : RouterID) :=
      InstIdent.internal s!"Router {rid}"

    let router_out (rid : RouterID) (dir : Dir rid) : InternalPort String :=
      { inst := router_internal rid, name := NatModule.stringify_output dir }

    let router_inp (rid : RouterID) (dir : Dir rid) : InternalPort String :=
      { inst := router_internal rid, name := NatModule.stringify_input dir }

    let mkrouter (rid : RouterID) : ExprLow String :=
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
      List.foldl (λ acc i => .product (mkrouter (Fin.mk i (by sorry))) acc) acc (List.range n.topology.netsz)

    let mkconn (acc : ExprLow String) (rid : RouterID) : ExprLow String :=
      List.foldlIdx
        (λ idx acc rid' => .connect
          {
            output  := router_out rid idx
            input   := sorry -- TODO: How do we know to which port of rid' we are connected?
          }
          acc)
        acc (n.topology.neigh rid)

    let mkconns (acc : ExprLow String) : ExprLow String :=
      List.foldl (λ acc i => mkconn acc (Fin.mk i (by sorry))) acc (List.range n.topology.netsz)

    .base { input := .nil, output := .nil } "empty"
    |> mkrouters

  -- We need an environment correctness property:
  --  · Each router is in the env, with correct amount of input/output
  --  · Each router implementation respect the specification given for a router

end DataflowRewriter.Noc
