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
abbrev Direction := Nat -- TODO: Proper type (enum? Fin?)

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

def Arbiter := (src : RouterID) → (dest : RouterID) → Option Nat

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
    .some 0 -- Local output
  else if src_x < dst_x then
    .some 1 -- West
  else if dst_x < src_x then
    .some 2 -- East
  else if src_y < dst_y then
    .some 3 -- North
  else if dst_y < src_y then
    .some 4 -- South
  else
    .none

def routerXY := router arbiterXY

def ε_noc : Env :=
  [
    (s!"Router 0", ⟨_, router arbiterXY 0⟩),
    (s!"Router 1", ⟨_, router arbiterXY 1⟩),
    (s!"Router 2", ⟨_, router arbiterXY 2⟩),
    (s!"Router 3", ⟨_, router arbiterXY 3⟩),
  ].toAssocList

@[drunfold_defs]
def noc_low : ExprLow String :=
  let internal (rID : RouterID) :=
    InstIdent.internal s!"Router {rID}"
  let internal_out (rId : RouterID) (dir : Nat) : InternalPort String :=
    { inst := internal rId, name := NatModule.stringify_output dir }
  let internal_inp (rId : RouterID) (dir : Nat) : InternalPort String :=
    { inst := internal rId, name := NatModule.stringify_input dir }
  let router (rId : RouterID) : ExprLow String := ExprLow.base
    {
      -- 0 is a special case since it is a local port
      input :=
        ⟨NatModule.stringify_input 0, NatModule.stringify_input rId⟩ ::
        List.map
          (λ n => ⟨NatModule.stringify_input (n + 1), (internal_inp rId) (n + 1)⟩)
          (List.range 4)
        |>.toAssocList,
      output :=
        ⟨NatModule.stringify_output 0, NatModule.stringify_output rId⟩ ::
        List.map
          (λ n => ⟨NatModule.stringify_output (n + 1), (internal_out rId) (n + 1)⟩)
          (List.range 4)
        |>.toAssocList,
    }
    s!"Router {rId}"
  let base :=
    router 0 |>
    ExprLow.product (router 1) |>
    ExprLow.product (router 2) |>
    ExprLow.product (router 3)
  let mkconnection_bi (a b : RouterID) (portA portB : Nat) (base : ExprLow String) :=
    ExprLow.connect
      { output := internal_out a portA, input := internal_inp b portB } base
    |>
    ExprLow.connect
      { output := internal_out b portB, input := internal_inp a portA }

  let mkconnection_we (w e : RouterID) (base : ExprLow String) :=
    mkconnection_bi w e 1 2 base
  let mkconnection_ns (n s : RouterID) (base : ExprLow String) :=
    mkconnection_bi n s 3 4 base
  base
  |> mkconnection_we 0 1
  |> mkconnection_we 2 3
  |> mkconnection_ns 0 2
  |> mkconnection_ns 1 3

def noc_lowT : Type := by
  precomputeTac [T| noc_low, ε_noc] by
    dsimp [drcomponents, ε_noc]
    dsimp [ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module']
    simp (disch := simpa) only [toString, drcompute]

def_module noc_lowM : StringModule noc_lowT :=
  [e| noc_low, ε_noc]
  reduction_by
    dsimp -failIfUnchanged [drunfold_defs, ExprHigh.extract, List.foldlM]
    rw [rw_opaque (by simp -failIfUnchanged (disch := simpa) only [drcompute]; rfl)]
    dsimp -failIfUnchanged [ ExprHigh.lower, ExprHigh.lower', ExprHigh.uncurry
          , ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module']
    skip
    rw [rw_opaque (by set_option trace.Meta.Tactic.simp.rewrite true in simp -implicitDefEqProofs -dsimp (disch := rfl) only [drcompute]; rfl)]
    dsimp [drcomponents]
    dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, AssocList.bijectivePortRenaming, AssocList.invertible, AssocList.keysList, AssocList.inverse, AssocList.filterId, AssocList.filter, List.inter];
    simp (disch := simp) only [drcompute, ↓reduceIte]
    dsimp [Module.product, Module.liftL, Module.liftR]
    dsimp [Module.connect']
    simp (disch := simp) only [drcompute]
    conv =>
      pattern (occs := *) Module.connect'' _ _
      all_goals
        rw [(Module.connect''_dep_rw (h := by simp (disch := simpa) only [AssocList.eraseAll_cons_neq,AssocList.eraseAll_cons_eq,AssocList.eraseAll_nil,PortMap.getIO,AssocList.find?_cons_eq,AssocList.find?_cons_neq]; dsimp -failIfUnchanged)
                                 (h' := by simp (disch := simpa) only [AssocList.eraseAll_cons_neq,AssocList.eraseAll_cons_eq,AssocList.eraseAll_nil,PortMap.getIO,AssocList.find?_cons_eq,AssocList.find?_cons_neq]; dsimp -failIfUnchanged))]

      unfold Module.connect''
      simp -failIfUnchanged only [drcompute]
      dsimp -failIfUnchanged
    dsimp -failIfUnchanged

    -- dsimp [noc_low, ε_noc]
    -- simp only [toString, String.reduceAppend]
    -- dsimp [ExprLow.build_module_expr, ExprLow.build_module, ExprLow.build_module']
    -- simp only [AssocList.find?]
    -- dsimp
    -- dsimp [drcomponents]
    -- dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, AssocList.bijectivePortRenaming, AssocList.invertible, AssocList.keysList, AssocList.inverse, AssocList.filterId, AssocList.filter, List.inter];
    -- simp (disch := simpa) only [drcompute]
    -- dsimp [
    --   -- List.range,
    --   -- List.range.loop, List.map, AssocList.mapKey,
    --   -- InternalPort.map,
    --   -- AssocList.find?,
    --   -- AssocList.eraseAll,
    --   -- AssocList.eraseAllP,
    --   -- AssocList.mapVal,
    --   Module.renamePorts,
    --   Module.product,
    --   Module.connect',
    --   Module.connect'',
    --   List.range,
    --   List.range.loop,
    --   toString, String.reduceAppend, drcomponents]
    -- simp (disch := simpa) only [drcompute]
    -- skip

-- Proof of correctness --------------------------------------------------------

end DataflowRewriter.Examples.NoC
