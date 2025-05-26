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

variable {α : Type} [BEq α] [LawfulBEq α]

abbrev Noc.routerT (n : Noc α) :=
  List n.Flit

abbrev Noc.nocT (n : Noc α) : Type :=
  Vector n.routerT n.netsz

@[drcomponents]
def Noc.input_rel (n : Noc α) (rid : n.RouterID) (val : n.Flit) (old_s new_s : n.nocT) : Prop :=
  new_s = old_s.set rid (old_s[rid] ++ [val])

@[drcomponents]
def Noc.output_rel (n : Noc α) (rid : n.RouterID) (dir : n.Dir rid) (val : n.Flit) (old_s new_s : n.nocT) : Prop :=
    let (dir', flit') := n.route rid val
    dir = dir' ∧ old_s = new_s.set rid (flit' :: new_s[rid])

@[drcomponents]
def Noc.mk_router_input (n : Noc α) (rid : n.RouterID) : RelIO n.nocT :=
  ⟨
    n.Data × n.RouterID,
    λ old_s inp new_s =>
      n.input_rel rid (inp.1, (n.mkhead rid inp.2 inp.1)) old_s new_s
  ⟩

@[drcomponents]
def Noc.mk_router_output (n : Noc α) (rid : n.RouterID) (dir : n.Dir rid) : RelIO n.nocT :=
  ⟨
    n.Data,
    λ old_s out new_s => ∃ head,
      n.output_rel rid dir (out, head) old_s new_s
  ⟩

@[drcomponents]
def Noc.mk_router_conn (n : Noc α) (rid : n.RouterID) : List (RelInt n.nocT) :=
  (n.neigh rid).mapFinIdx (λ dir rid' Hdir =>
    λ old_s new_s => ∃ val mid_s,
      n.output_rel rid (Fin.mk (dir + 1) (by simpa)) val old_s mid_s ∧
      n.input_rel rid' val mid_s new_s)

@[drcomponents]
def Noc.build_module (n : Noc α) : Module Nat (Vector n.routerT n.netsz) :=
  {
    inputs := RelIO.liftFinf n.netsz n.mk_router_input
    outputs := RelIO.liftFinf n.netsz (λ rid => n.mk_router_output rid n.DirLocal)
    internals := RelInt.liftFinf n.netsz n.mk_router_conn,
    init_state := λ s => s = Vector.replicate n.netsz [],
  }
