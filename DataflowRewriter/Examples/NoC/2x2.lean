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

@[simp] abbrev Data := ℕ
@[simp] abbrev FlitHeader := Nat -- TODO: Dest RouterID
@[simp] abbrev RouterID := Nat -- TODO: a Fin probably
@[simp] abbrev netsz := 4
-- TODO: Proper type? Enum ? Fin ?i
@[simp] abbrev Dir := Nat
@[simp] abbrev DirLocal := 0
@[simp] abbrev DirWest  := 1
@[simp] abbrev DirEast  := 2
@[simp] abbrev DirNorth := 3
@[simp] abbrev DirSouth := 4

@[simp] abbrev Flit := Data × FlitHeader

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
    (s!"Sink Flit 8", ⟨_, StringModule.sink Flit 8⟩), -- Sink for unused i/o
    (s!"Router 0",    ⟨_, router arbiterXY 0⟩),       -- Top left router
    (s!"Router 1",    ⟨_, router arbiterXY 1⟩),       -- Top right router
    (s!"Router 2",    ⟨_, router arbiterXY 2⟩),       -- Bot left router
    (s!"Router 3",    ⟨_, router arbiterXY 3⟩),       -- Bot right router
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
      -- 0 is a special case (Local port)
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

  -- Make a bidirectional connection between two routers
  let mkconn_bi (a b : RouterID) (portA portB : Nat) (base : ExprLow String) :=
    ExprLow.connect
      { output := router_internal_out a portA, input := router_internal_inp b portB } base
    |>
    ExprLow.connect
      { output := router_internal_out b portB, input := router_internal_inp a portA }

  let sink_internal_inp (sId : Nat) :=
    { inst := InstIdent.internal "Sink", name := NatModule.stringify_input sId }

  -- We use sinks to discard unconnected ports of our routers
  let mksink : ExprLow String := ExprLow.base
    {
      input :=
        List.range 7
        |>.map (λ n => ⟨NatModule.stringify_input 0, sink_internal_inp n⟩)
        |>.toAssocList,
      output := .nil,
    }
    s!"Sink Flit 8"

  -- Connect an output of a router to a sink
  let mkconn_sink (rId : RouterID) (sId : Nat) (dir : Dir) (base : ExprLow String) :=
    ExprLow.connect
      { output := router_internal_out rId dir, input := sink_internal_inp sId }
      base

  mksink                          |>  -- Sink for unused i/o
  ExprLow.product (mkrouter 0)    |>  -- Top left router
  ExprLow.product (mkrouter 1)    |>  -- Top right router
  ExprLow.product (mkrouter 2)    |>  -- Bot left router
  ExprLow.product (mkrouter 3)    |>  -- Bot right router
  mkconn_bi 0 1 DirEast DirWest   |>
  mkconn_bi 2 3 DirEast DirWest   |>
  mkconn_bi 0 2 DirSouth DirNorth |>
  mkconn_bi 1 3 DirSouth DirNorth |>
  mkconn_sink 0 0 DirNorth        |>
  mkconn_sink 0 1 DirWest         |>
  mkconn_sink 1 2 DirNorth        |>
  mkconn_sink 1 3 DirEast         |>
  mkconn_sink 2 4 DirSouth        |>
  mkconn_sink 2 5 DirWest         |>
  mkconn_sink 3 6 DirSouth        |>
  mkconn_sink 3 7 DirEast

def noc_lowT : Type := by
  precomputeTac [T| noc_low, ε_noc] by
    dsimp [noc_low, ε_noc]
    dsimp [ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module']
    simp (disch := simpa) only [toString, drcompute]

@[simp] theorem sink_in_ε :
  AssocList.find? "Sink Flit 8" ε_noc = .some ⟨_, StringModule.sink Flit 8⟩ := rfl

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

set_option maxHeartbeats 1000000 in
set_option profiler true in
def_module noc_lowM : StringModule noc_lowT :=
  [e| noc_low, ε_noc]
  reduction_by
    dsimp -failIfUnchanged [drunfold_defs, ExprHigh.extract, List.foldlM]
    dsimp [toString, drcompute, List.range, List.map, List.range.loop, NatModule.stringify_output, NatModule.stringify_input]
    rw [rw_opaque (by dsimp [ ExprHigh.lower, ExprHigh.lower', ExprHigh.uncurry
                            , ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module'])]
    dsimp [toString, drcompute, List.range, List.map, List.range.loop, NatModule.stringify_output, NatModule.stringify_input, drcomponents]
    dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts]
    dsimp [Module.product, Module.liftL, Module.liftR]
    dsimp [Module.connect']
    -- conv => arg 1; arg 1; whnf
    simp (disch := solve | trivial | simp | rfl) only [drcompute]
    conv =>
      pattern (occs := *) Module.connect'' _ _
      all_goals
        rw [(Module.connect''_dep_rw (h := by conv => rhs; whnf)
                                     (h' := by conv => rhs; whnf))]
    unfold Module.connect''
    dsimp
    skip

#check noc_lowM
-- set_option pp.deepTerms true in
-- set_option pp.maxSteps 1000000 in
-- #print noc_lowM

-- Proof of correctness --------------------------------------------------------

instance : MatchInterface noc_lowM noc where
  input_types := by sorry
  output_types := by sorry
  inputs_present := by sorry
  outputs_present := by sorry

def φ (I : noc_lowT) (S : nocT) : Prop :=
  False

theorem noc_low_refines_initial :
  Module.refines_initial noc_lowM noc φ := by
    sorry

theorem noc_low_refines_φ : noc_lowM ⊑_{φ} noc := by
  sorry

theorem noc_low_ϕ_indistinguishable :
  ∀ i s, φ i s → Module.indistinguishable noc_lowM noc i s := by
    sorry

theorem noc_low_correct : noc_lowM ⊑ noc := by
  apply (
    Module.refines_φ_refines
      noc_low_ϕ_indistinguishable
      noc_low_refines_initial
      noc_low_refines_φ
  )

end DataflowRewriter.Examples.NoC
