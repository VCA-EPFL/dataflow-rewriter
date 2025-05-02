import Lean
import Init.Data.BitVec.Lemmas
import Qq

import DataflowRewriter.Module
import DataflowRewriter.Component
import DataflowRewriter.ModuleReduction
import DataflowRewriter.ExprLow
import DataflowRewriter.ExprLowLemmas

open Batteries (AssocList)

namespace DataflowRewriter.Examples.NoC

-- This file implement a non-parameterized 2x2 Noc

abbrev Data := ℕ
abbrev FlitHeader := Nat -- TODO: Dest RouterID
abbrev RouterID := Nat -- TODO: a Fin probably
abbrev netsz := 4
-- TODO: Proper type? Enum ? Fin ?
abbrev Dir := Nat
abbrev DirLocal := 0
abbrev DirWest  := 1
abbrev DirEast  := 2
abbrev DirNorth := 3
abbrev DirSouth := 4

abbrev Flit := Data × FlitHeader

-- Specification ---------------------------------------------------------------

@[drcomponents]
def lift_f {S : Type} (n : ℕ) (f : ℕ → (Σ T : Type, S → T → S → Prop)) : PortMap ℕ (Σ T : Type, (S → T → S → Prop)) :=
  List.range n |>.map (λ i => ⟨↑i, f i⟩) |>.toAssocList

def nocT : Type :=
  List Flit

@[drcomponents]
def mk_noc_input_rule (rID : RouterID) : Σ T : Type, nocT → T → nocT → Prop :=
    ⟨Flit, λ oldState v newState => newState = oldState.concat v⟩

@[drcomponents]
def mk_noc_output_rule (rID : RouterID) : Σ T : Type, nocT → T → nocT → Prop :=
    ⟨
      Data,
      λ oldState data newState =>
        ∃ i, newState = oldState.remove i ∧
        (data, rID) = oldState.get i
    ⟩

@[drcomponents]
def noc' (name := "noc") : NatModule (NatModule.Named name nocT) :=
  {
    inputs := lift_f netsz mk_noc_input_rule,
    outputs := lift_f netsz mk_noc_output_rule,
    init_state := λ s => s = [],
  }

@[drcomponents] def noc := noc' |>.stringify

-- Implementation --------------------------------------------------------------

def Arbiter := (src : RouterID) → (dest : RouterID) → Option Dir

def routerT := List Flit

@[drcomponents]
def mk_router_input (_ : ℕ) : Σ T : Type, routerT → T → routerT → Prop :=
  ⟨Flit, λ oldS inp newS => newS = oldS.concat inp⟩

@[drcomponents]
def mk_router_output (arbiter : Arbiter) (rId : RouterID) (n : ℕ) : Σ T : Type, routerT → T → routerT → Prop :=
  ⟨Flit, λ oldS out newS => oldS = out :: newS ∧ arbiter rId out.2 = n⟩

@[drcomponents]
def router' (arbiter : Arbiter) (rId : RouterID) (name := "routerXY") : NatModule (NatModule.Named name nocT) :=
  {
    inputs := lift_f 5 mk_router_input,
    outputs := lift_f 5 (mk_router_output arbiter rId),
    init_state := λ s => s = [],
  }

@[drcomponents] def router arbiter rId := (router' arbiter rId) |>.stringify

def getX (rId : RouterID) := rId.mod 2

def getY (rId : RouterID) := rId.div 2

def arbiterXY : Arbiter := λ src dst =>
  let src_x := getX src
  let src_y := getY src
  let dst_x := getX dst
  let dst_y := getY dst
  if src_x == dst_x && src_y == dst_y then
    .some DirLocal
  else if src_x < dst_x then
    .some DirWest
  else if dst_x < src_x then
    .some DirEast
  else if src_y < dst_y then
    .some DirNorth
  else if dst_y < src_y then
    .some DirSouth
  else
    .none

def routerXY := router arbiterXY

def ε_noc : Env :=
  [
    (s!"Sink Flit", ⟨_, StringModule.sink Flit⟩), -- Sink for unused i/o
    (s!"Router 0",  ⟨_, router arbiterXY 0⟩),     -- Top left router
    (s!"Router 1",  ⟨_, router arbiterXY 1⟩),     -- Top right router
    (s!"Router 2",  ⟨_, router arbiterXY 2⟩),     -- Bot left router
    (s!"Router 3",  ⟨_, router arbiterXY 3⟩),     -- Bot right router
  ].toAssocList

@[drunfold_defs]
def noc_low : ExprLow String :=

  let router_internal (rId : RouterID) :=
    InstIdent.internal s!"Router {rId}"

  let router_internal_out (rId : RouterID) (dir : Dir) : InternalPort String :=
    { inst := router_internal rId, name := NatModule.stringify_output dir }

  let router_internal_inp (rId : RouterID) (dir : Dir) : InternalPort String :=
    { inst := router_internal rId, name := NatModule.stringify_input dir }

  let mkrouter (rId : RouterID) : ExprLow String := ExprLow.base
    {
      -- 0 is a special case : The local port
      input :=
        ⟨NatModule.stringify_input DirLocal, NatModule.stringify_input rId⟩ ::
        List.map
          (λ n => ⟨NatModule.stringify_input (n + 1), (router_internal_inp rId) (n + 1)⟩)
          (List.range 4)
        |>.toAssocList,
      output :=
        ⟨NatModule.stringify_output DirLocal, NatModule.stringify_output rId⟩ ::
        List.map
          (λ n => ⟨NatModule.stringify_output (n + 1), (router_internal_out rId) (n + 1)⟩)
          (List.range 4)
        |>.toAssocList,
    }
    s!"Router {rId}"

  let sink_internal (sId : Nat) :=
    InstIdent.internal s!"Sink {sId}"

  let sink_internal_inp (sId : Nat) :=
    { inst := sink_internal sId, name := NatModule.stringify_input 0 }

  -- We use sinks to discard unconnected ports of our routers
  let mksink (sId : Nat) : ExprLow String := ExprLow.base
    {
      input := [⟨NatModule.stringify_input 0, sink_internal_inp sId⟩].toAssocList,
      output := .nil,
    }
    s!"Sink Flit"

  -- Make a bidirectional connection between two routers
  let mkconn_bi (a b : RouterID) (portA portB : Nat) (base : ExprLow String) :=
    ExprLow.connect
      { output := router_internal_out a portA, input := router_internal_inp b portB } base
    |>
    ExprLow.connect
      { output := router_internal_out b portB, input := router_internal_inp a portA }

  -- West - East connection
  let mkconn_we (w e : RouterID) (base : ExprLow String) :=
    mkconn_bi w e 1 2 base

  -- North -- South connection
  let mkconn_ns (n s : RouterID) (base : ExprLow String) :=
    mkconn_bi n s 3 4 base

  -- Connect an output of a router to a sink
  let mkconn_sink (rId : RouterID) (sId : Nat) (dir : Dir) (base : ExprLow String) :=
    ExprLow.connect
      { output := router_internal_out rId dir, input := sink_internal_inp sId }
      base

  mkrouter 0                    |>  -- Top left router
  ExprLow.product (mkrouter 1)  |>  -- Top right router
  ExprLow.product (mkrouter 2)  |>  -- Bot left router
  ExprLow.product (mkrouter 3)  |>  -- Bot right router
  ExprLow.product (mksink 0)    |>  -- 0 North
  ExprLow.product (mksink 1)    |>  -- 0 West
  ExprLow.product (mksink 2)    |>  -- 1 North
  ExprLow.product (mksink 3)    |>  -- 1 East
  ExprLow.product (mksink 4)    |>  -- 2 South
  ExprLow.product (mksink 5)    |>  -- 2 West
  ExprLow.product (mksink 6)    |>  -- 3 South
  ExprLow.product (mksink 7)    |>  -- 3 East
  mkconn_we 0 1                 |>
  mkconn_we 2 3                 |>
  mkconn_ns 0 2                 |>
  mkconn_ns 1 3                 |>
  mkconn_sink 0 0 DirNorth      |>
  mkconn_sink 0 1 DirWest       |>
  mkconn_sink 1 2 DirNorth      |>
  mkconn_sink 1 3 DirEast       |>
  mkconn_sink 2 4 DirSouth      |>
  mkconn_sink 2 5 DirWest       |>
  mkconn_sink 3 6 DirSouth      |>
  mkconn_sink 3 7 DirEast

def noc_lowT : Type := by
  precomputeTac [T| noc_low, ε_noc] by
    dsimp [noc_low, ε_noc]
    dsimp [ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module']
    simp (disch := simpa) only [toString, drcompute]

@[simp] theorem sink_in_ε :
  AssocList.find? "Sink Flit" ε_noc = .some ⟨_, StringModule.sink Flit⟩ := rfl

@[simp] theorem router_in_ε_0 :
  AssocList.find? "Router 0" ε_noc = .some ⟨_, router arbiterXY 0⟩ := rfl

@[simp] theorem router_in_ε_1 :
  AssocList.find? "Router 1" ε_noc = .some ⟨_, router arbiterXY 1⟩ := rfl

@[simp] theorem router_in_ε_2 :
  AssocList.find? "Router 2" ε_noc = .some ⟨_, router arbiterXY 2⟩ := rfl

@[simp] theorem router_in_ε_3 :
  AssocList.find? "Router 3" ε_noc = .some ⟨_, router arbiterXY 3⟩ := rfl

@[drcompute]
axiom bijectivePortRenaming_invert' {α} [DecidableEq α] {p : AssocList α α} {i : α}:
  p.bijectivePortRenaming i = ((p.filterId.append p.inverse.filterId).find? i).getD i

attribute [-drcompute] AssocList.bijectivePortRenaming_invert

def_module noc_lowM : StringModule noc_lowT :=
  [e| noc_low, ε_noc]
  reduction_by
    dsimp -failIfUnchanged [drunfold_defs, ExprHigh.extract, List.foldlM, drcomponents]
    rw [rw_opaque (by simp -failIfUnchanged (disch := simpa) only [drcompute, toString, InternalPort.map]; rfl)]
    dsimp -failIfUnchanged [ ExprHigh.lower, ExprHigh.lower', ExprHigh.uncurry
          , ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module']

    dsimp only [toString, drcompute, List.range, List.map, List.range.loop]
    simp (disch := solve | simp | rfl | simpa) only [toString, drcompute, List.range, List.map, List.range.loop, drcomponents]
    dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts];
    simp (disch := solve | simp | rfl) only [toString, drcompute, List.range, List.map, List.range.loop, drcomponents]
    dsimp [Module.product, Module.liftL, Module.liftR]
    dsimp [Module.connect']
    simp (disch := simp) only [drcompute]
    conv =>
      pattern (occs := *) Module.connect'' _ _
      all_goals
        rw [(Module.connect''_dep_rw (h := by conv => rhs; whnf)
                                     (h' := by conv => rhs; whnf))]
    skip

-- Proof of correctness --------------------------------------------------------

end DataflowRewriter.Examples.NoC
