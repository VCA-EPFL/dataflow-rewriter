/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import Graphiti.Module
import Graphiti.Component
import Graphiti.Examples.Noc.Utils
import Graphiti.Examples.Noc.Lang

open Batteries (AssocList)

namespace Graphiti.Noc

  variable {Data : Type} [BEq Data] [LawfulBEq Data] {netsz : Netsz}

  @[drcomponents]
  def router_name (n : Noc Data netsz) (rid : n.topology.RouterID) :=
    s!"Router {rid}"

  @[drcomponents]
  def router_stringify_inp (n : Noc Data netsz) (rid : n.topology.RouterID) (dir : Nat) :=
    s!"Router {rid} in{dir}"

  @[drcomponents]
  def router_stringify_out (n : Noc Data netsz) (rid : n.topology.RouterID) (dir : Nat) :=
    s!"Router {rid} out{dir}"

  @[drunfold_defs]
  def Noc.build_expr (n : Noc Data netsz) : ExprLow String :=

    let mkrouter (rid : n.RouterID) : ExprLow String :=
      .base { input := .nil, output := .nil } s!"Router {rid}"

    let mkrouters (acc : ExprLow String) : ExprLow String :=
      List.foldr (λ i acc => .product (mkrouter i) acc) acc (fin_range netsz)

    let mkconns (acc : ExprLow String) : ExprLow String :=
      List.foldr
        (λ c acc =>
          let rid_out := c.1
          let rid_inp := c.2.1
          let dir_out := c.2.2.1
          let dir_inp := c.2.2.2
          .connect
            {
              output  := router_stringify_out n rid_out dir_out
              input   := router_stringify_inp n rid_inp dir_inp
            }
          acc)
        acc n.topology.conns

    .base { input := .nil, output := .nil } "empty"
    |> mkrouters
    |> mkconns

end Graphiti.Noc
