import Lean
import Init.Data.BitVec.Lemmas
import Qq

import DataflowRewriter.Module
import DataflowRewriter.Component

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
def router (arbiter : Arbiter) (rId : RouterID) (name := "routerXY") : NatModule (NatModule.Named name nocT) :=
  {
    inputs := lift_f 5 mk_router_input,
    outputs := lift_f 5 (mk_router_output arbiter rId),
    init_state := λ s => s = [],
  }

-- TODO: Return x coordinates in a 2x2 mesh
def getX (rId : RouterID) := 0

-- TODO: Return y coordinates in a 2x2 mesh
def getY (rId : RouterID) := 0

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
-- TODO, but we need a mapping from routerID to x and y position

def routerXY := router arbiterXY

-- TODO: Create a NoC by creating 4 routers and connecting them
def noc_low' : ExprLow String :=
  sorry -- TODO

-- Proof of correctness --------------------------------------------------------

end DataflowRewriter.Examples.NoC
