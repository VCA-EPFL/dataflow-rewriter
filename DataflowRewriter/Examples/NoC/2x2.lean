import Lean
import Init.Data.BitVec.Lemmas
import Qq

import DataflowRewriter.Module
import DataflowRewriter.Component
import DataflowRewriter.ModuleReduction
import DataflowRewriter.ExprLow
import DataflowRewriter.ExprLowLemmas

import DataflowRewriter.Examples.NoC.BasicLemmas

open Batteries (AssocList)

namespace DataflowRewriter.Examples.NoC

-- This file implement a non-parameterized 2x2 Noc

@[simp] abbrev Data := ℕ
@[simp] abbrev FlitHeader := Nat -- TODO: Dest RouterID
@[simp] abbrev RouterID := Nat -- TODO: a Fin probably
@[simp] abbrev netsz := 4
-- TODO: Proper type? Enum ? Fin ?
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
def mk_noc_input_rule (rId : RouterID) : Σ T : Type, nocT → T → nocT → Prop :=
    ⟨Flit, λ oldState v newState => newState = oldState.concat v⟩

@[drcomponents]
def mk_noc_output_rule (rId : RouterID) : Σ T : Type, nocT → T → nocT → Prop :=
    ⟨
      Flit,
      λ oldState out newState =>
        out.2 = rId ∧ ∃ i, newState = oldState.remove i ∧ out = oldState.get i
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
def mk_router_input (rId : ℕ) : Σ T : Type, routerT → T → routerT → Prop :=
  ⟨Flit, λ oldS inp newS => newS = oldS.concat inp⟩

@[drcomponents]
def mk_router_output (arbiter : Arbiter) (rId : RouterID) (n : ℕ) : Σ T : Type, routerT → T → routerT → Prop :=
  ⟨Flit, λ oldS out newS => oldS = out :: newS ∧ arbiter rId out.2 = n⟩

@[drcomponents]
def router' (arbiter : Arbiter) (rId : RouterID) (name := "router") : NatModule (NatModule.Named name nocT) :=
  {
    inputs := lift_f 5 mk_router_input,
    outputs := lift_f 5 (mk_router_output arbiter rId),
    init_state := λ s => s = [],
  }

@[drcomponents]
def router_stringify_inp (rId : RouterID) (n : ℕ) :=
  s!"Router {rId} in{n + 1}"

@[drcomponents]
def router_stringify_out (rId : RouterID) (n : ℕ) :=
  s!"Router {rId} out{n + 1}"

@[drcomponents]
def router (arbiter : Arbiter) (rId : RouterID) (name := "router") : StringModule (NatModule.Named name nocT) :=
  router' arbiter rId |>.mapIdent (router_stringify_inp rId) (router_stringify_out rId)

-- Contrary to a `sink`, a `hide` never consume its i/o
@[drcomponents]
def hide' (T : Type _) (inp_sz out_sz : Nat) (name := "hide") : NatModule (NatModule.Named name Unit) :=
  {
    inputs := List.range inp_sz |>.map (λ n => ⟨n, ⟨T, λ _ _ _ => False⟩⟩) |>.toAssocList,
    outputs := List.range out_sz |>.map (λ n => ⟨n, ⟨T, λ _ _ _ => False⟩⟩) |>.toAssocList,
    init_state := λ _ => True,
  }

@[drcomponents] def hide T inp_sz out_sz := (hide' T inp_sz out_sz) |>.stringify

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
    (s!"Hide Flit 8 8", ⟨_, hide Flit 8 8⟩),      -- Hide unused i/o
    (s!"Router 0",      ⟨_, router arbiterXY 0⟩), -- Top left router
    (s!"Router 1",      ⟨_, router arbiterXY 1⟩), -- Top right router
    (s!"Router 2",      ⟨_, router arbiterXY 2⟩), -- Bot left router
    (s!"Router 3",      ⟨_, router arbiterXY 3⟩), -- Bot right router
  ].toAssocList

@[drunfold_defs]
def noc_low : ExprLow String :=

  let router_internal (rId : RouterID) :=
    InstIdent.internal s!"Router {rId}"

  let router_out (rId : RouterID) (dir : Dir) : InternalPort String :=
    { inst := router_internal rId, name := NatModule.stringify_output dir }

  let router_inp (rId : RouterID) (dir : Dir) : InternalPort String :=
    { inst := router_internal rId, name := NatModule.stringify_input dir }

  let mkrouter (rId : RouterID) : ExprLow String := ExprLow.base
    {
      input :=
        AssocList.cons (router_stringify_inp rId 0) (NatModule.stringify_input rId)
          (List.map
            (λ n => ⟨router_stringify_inp rId (n + 1), router_inp rId (n + 1)⟩)
            (List.range 4)
          |>.toAssocList),
      output :=
        AssocList.cons (router_stringify_out rId 0) (NatModule.stringify_output rId)
          (List.map
            (λ n => ⟨router_stringify_out rId (n + 1), router_out rId (n + 1)⟩)
            (List.range 4)
          |>.toAssocList),
    }
    s!"Router {rId}"

  -- Make a bidirectional connection between two routers
  let mkconn_bi (a b : RouterID) (portA portB : Nat) (base : ExprLow String) :=
    base |>
    ExprLow.connect { output := router_out a portA, input := router_inp b portB } |>
    ExprLow.connect { output := router_out b portB, input := router_inp a portA }

  let hide_inp (sId : Nat) : InternalPort String :=
    { inst := InstIdent.internal "Hide", name := NatModule.stringify_input sId }

  let hide_out (sId : Nat) : InternalPort String :=
    { inst := InstIdent.internal "Hide", name := NatModule.stringify_output sId }

  let mkhide : ExprLow String := ExprLow.base
    {
      input :=
        List.range 8
        |>.map (λ n => ⟨NatModule.stringify_input n, hide_inp n⟩)
        |>.toAssocList,
      output :=
        List.range 8
        |>.map (λ n => ⟨NatModule.stringify_output n, hide_out n⟩)
        |>.toAssocList,
    }
    s!"Hide Flit 8 8"

  -- Connect an output and input of a router in a direction to hide
  let mkconn_hide (rId : RouterID) (sId : Nat) (dir : Dir) (base : ExprLow String) :=
    base |>
    ExprLow.connect { output := router_out rId dir, input := hide_inp sId } |>
    ExprLow.connect { output := hide_out sId, input := router_inp rId dir }

  mkhide                          |>  -- Hide unused i/o
  ExprLow.product (mkrouter 0)    |>  -- Top left router
  ExprLow.product (mkrouter 1)    |>  -- Top right router
  ExprLow.product (mkrouter 2)    |>  -- Bot left router
  ExprLow.product (mkrouter 3)    |>  -- Bot right router
  mkconn_bi 0 1 DirEast DirWest   |>
  mkconn_bi 2 3 DirEast DirWest   |>
  mkconn_bi 0 2 DirSouth DirNorth |>
  mkconn_bi 1 3 DirSouth DirNorth |>
  mkconn_hide 0 0 DirNorth        |>
  mkconn_hide 0 1 DirWest         |>
  mkconn_hide 1 2 DirNorth        |>
  mkconn_hide 1 3 DirEast         |>
  mkconn_hide 2 4 DirSouth        |>
  mkconn_hide 2 5 DirWest         |>
  mkconn_hide 3 6 DirSouth        |>
  mkconn_hide 3 7 DirEast

def noc_lowT : Type := by
  precomputeTac [T| noc_low, ε_noc] by
    dsimp [noc_low, ε_noc]
    dsimp [ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module']
    simp (disch := simpa) only [toString, drcompute]

@[drenv] theorem hide_in_ε :
  AssocList.find? "Hide Flit 8 8" ε_noc = .some ⟨_, hide Flit 8 8⟩ := rfl

@[drenv] theorem router_in_ε_0 :
  AssocList.find? "Router 0" ε_noc = .some ⟨_, router arbiterXY 0⟩ := rfl

@[drenv] theorem router_in_ε_1 :
  AssocList.find? "Router 1" ε_noc = .some ⟨_, router arbiterXY 1⟩ := rfl

@[drenv] theorem router_in_ε_2 :
  AssocList.find? "Router 2" ε_noc = .some ⟨_, router arbiterXY 2⟩ := rfl

@[drenv] theorem router_in_ε_3 :
  AssocList.find? "Router 3" ε_noc = .some ⟨_, router arbiterXY 3⟩ := rfl

def_module noc_lowM : StringModule noc_lowT :=
  [e| noc_low, ε_noc]
  reduction_by
    dr_reduce_module
    simp only [drlogic]

-- Useful lemmas ---------------------------------------------------------------

axiom perm_in_perm_l {α} {l1 l2 : List α} {v} {H : l1.Perm l2} (Hin : v ∈ l2 := by simp):
  ∃ i : Fin l1.length, l1[i] = v

theorem perm_in_perm_r {α} {l1 l2 : List α} {v} {H : l1.Perm l2} (Hin : v ∈ l1 := by simpa) :
  ∃ i : Fin l2.length, l2[i] = v := by
    apply perm_in_perm_l
    · rw [List.perm_comm]
    · sorry

theorem getX_getY_correct {rId dst : RouterID} :
  getX rId = getX dst → getY rId = getY dst → dst = rId := by
    intro H1 H2
    dsimp [getX] at H1
    dsimp [getY] at H2
    sorry -- Annoying

theorem arbiterXY_correct (rId dst : RouterID) :
  arbiterXY rId dst = DirLocal → dst = rId := by
    dsimp [arbiterXY]
    cases Heq : (getX rId == getX dst && getY rId == getY dst)
    · sorry -- Contradiction, a bit annoying
    · dsimp
      intros _
      simp only [Bool.and_eq_true, beq_iff_eq] at Heq
      obtain ⟨HeqX, HeqY⟩ := Heq
      apply getX_getY_correct HeqX HeqY

-- Proof of correctness --------------------------------------------------------

instance : MatchInterface noc_lowM noc  := by
  dsimp [noc_lowM, noc]
  solve_match_interface

def φ (I : noc_lowT) (S : nocT) : Prop :=
  List.Perm S (I.1 |> I.2.1.append |> I.2.2.1.append |> I.2.2.2.1.append)

theorem perm_in_perm_φ {I : noc_lowT} {S : nocT} {v} {Hφ : φ I S} :
  v ∈ (I.1 |> I.2.1.append |> I.2.2.1.append |> I.2.2.2.1.append)
  → ∃ i : Fin S.length, List.get S i = v := by
    apply perm_in_perm_l; exact Hφ

theorem noc_low_refines_initial :
  Module.refines_initial noc_lowM noc φ := by
    intros i Hi
    dsimp [noc_lowM] at Hi
    exists []
    simpa [φ, Hi, drcompute, drcomponents]

theorem noc_low_refines_φ : noc_lowM ⊑_{φ} noc := by
  intros i s H
  constructor
  · intros ident mid_i v Hrule
    case_transition Hcontains : (Module.inputs noc_lowM), ident,
     (PortMap.getIO_not_contained_false' Hrule)
    simp only [
      noc_lowM,
      AssocList.contains_eq, AssocList.toList,
      List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq
    ] at Hcontains
    rcases Hcontains with H | H | H | H
    <;> subst ident
    <;> dsimp [noc_lowM, drcompute] at Hrule v ⊢
    <;> unfold φ at *
    <;> dsimp only [List.append_eq] at *
    <;> exists (List.concat s v)
    <;> exists (List.concat s v)
    <;> and_intros
    <;> try rfl
    all_goals dsimp [drcomponents]
    all_goals try constructor; done
    all_goals simp only [List.concat_eq_append] at *
    · obtain ⟨Hrule1, Hrule2⟩ := Hrule
      rw [Hrule1, ←Hrule2]
      repeat rw [←List.append_assoc]
      repeat rw [←List.append_assoc] at H
      rwa [List.perm_append_right_iff (l := [v])]
    · obtain ⟨⟨Hrule1, Hrule2⟩, Hrule3⟩ := Hrule
      rw [←Hrule3, Hrule1, ←Hrule2]
      repeat rw [←List.append_assoc]
      repeat rw [←List.append_assoc] at H
      sorry
    · obtain ⟨⟨⟨Hrule1, Hrule2⟩, Hrule3⟩, Hrule4⟩ := Hrule
      rw [Hrule1, ←Hrule2, ←Hrule3, ←Hrule4]
      sorry
    · obtain ⟨⟨⟨Hrule1, Hrule2⟩, Hrule3⟩, Hrule4⟩ := Hrule
      rw [Hrule1, ←Hrule2, ←Hrule3, ←Hrule4]
      repeat rw [←List.append_assoc]
      repeat rw [←List.append_assoc] at H
      sorry
  · intros ident mid_i v Hrule
    case_transition Hcontains : (Module.outputs noc_lowM), ident,
     (PortMap.getIO_not_contained_false' Hrule)
    simp only [
      noc_lowM,
      AssocList.contains_eq, AssocList.toList,
      List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq
    ] at Hcontains
    rcases Hcontains with H | H | H | H
    <;> subst ident
    <;> dsimp [noc_lowM, drcompute] at Hrule v ⊢
    <;> unfold φ at *
    <;> dsimp only [List.append_eq] at *
    -- TODO: In all of these cases, we need to remove v from s, some part is
    -- annoying to prove
    · obtain ⟨⟨H1, H2⟩, H3⟩ := Hrule
      rw [H1, H3] at H
      dsimp [arbiterXY, getX, getY] at H2
      repeat rw [←List.append_assoc]
      repeat rw [←List.append_assoc] at H
      sorry
    · obtain ⟨⟨⟨H1, H2⟩, H3⟩, H4⟩ := Hrule
      rw [H1, H3, H4] at H
      dsimp [List.append_eq] at H ⊢
      repeat rw [←List.append_assoc]
      repeat rw [←List.append_assoc] at H
      sorry
    · obtain ⟨⟨⟨⟨H1, H2⟩, H3⟩, H4⟩, H5⟩ := Hrule
      rw [H1, H3, H4, H5] at H
      dsimp [List.append_eq] at H ⊢
      repeat rw [←List.append_assoc]
      repeat rw [←List.append_assoc] at H
      sorry
    · obtain ⟨⟨⟨⟨H1, H2⟩, H3⟩, H4⟩, H5⟩ := Hrule
      rw [H1, H3, H4] at H
      repeat rw [←List.append_assoc]
      repeat rw [←List.append_assoc] at H
      sorry
  · intros rule mid_i H1 H2
    simp only [noc_lowM, List.mem_cons, List.not_mem_nil] at H1
    simp only [or_false, or_self_left] at H1
    rcases H1 with H1 | H1 | H1 | H1 | H1 | H1 | H1 | H1 | H1
    <;> subst rule
    <;> dsimp [drcomponents]
    <;> exists s
    <;> constructor
    <;> try (constructor; done)
    all_goals unfold φ at *
    all_goals obtain ⟨consumed_output, output, H⟩ := H2
    -- TODO: We need annoying permutations lemmas
    · obtain ⟨⟨⟨H1, H2⟩, H3⟩, ⟨⟨H4, H5⟩, H6⟩, H7⟩ := H
      rw [H4, ←H5, ←H6, ←H7,]
      rw [H1, H3] at H
      dsimp at H ⊢
      -- ok
      sorry
    · obtain ⟨⟨⟨⟨⟨H1, H2⟩, H3⟩, H4⟩, H5⟩, H6, H7⟩ := H
      rw [H1, H3, H4, H5] at H
      rw [H6, ←H7]
      dsimp at H ⊢
      -- ok
      sorry
    · obtain ⟨⟨⟨⟨H1, H2⟩, H3⟩, H4⟩, ⟨⟨H5, H6⟩, H7⟩, H8⟩ := H
      rw [H1, H3, H4] at H
      rw [H5, ←H6, ←H7, ←H8]
      dsimp at H ⊢
      -- ok
      sorry
    · obtain ⟨⟨⟨⟨⟨H1, H2⟩, H3⟩, H4⟩, H5⟩, ⟨H6, H7⟩, H8⟩ := H
      rw [H1, H3, H4, H5] at H
      rw [H6, ←H7, ←H8]
      dsimp at H ⊢
      -- ok
      sorry
    · obtain ⟨⟨⟨H1, H2⟩, H3⟩, ⟨H4, H5⟩, H6⟩ := H
      rw [H1, H3] at H
      rw [H4, ←H5, ←H6]
      dsimp at H ⊢
      simpa
    · obtain ⟨⟨⟨⟨H1, H2⟩, H3⟩, H4⟩, H5, H6⟩ := H
      rw [H1, H3, H4] at H
      rw [H5, ←H6]
      dsimp at H ⊢
      -- ok
      sorry
    · obtain ⟨⟨⟨⟨⟨H1, H2⟩, H3⟩, H4⟩, H5⟩, ⟨⟨H6, H7⟩, H8⟩, H9⟩ := H
      rw [H1, H3, H4, H5] at H
      rw [H6, ←H7, ←H8, ←H9]
      dsimp at H ⊢
      simpa
    · obtain ⟨⟨⟨⟨⟨H1, H2⟩, H3⟩, H4⟩, H5⟩, ⟨⟨H6, H7⟩, H8⟩, H9⟩ := H
      rw [H1, H3, H4, H5] at H
      rw [H6, ←H7, ←H8, ←H9]
      dsimp at H ⊢
      -- ok
      sorry

theorem noc_low_ϕ_indistinguishable :
  ∀ i s, φ i s → Module.indistinguishable noc_lowM noc i s := by
    intros i s H
    constructor
    <;> intros ident new_i v Hrule
    <;> dsimp [drcomponents, noc_lowM, List.range, List.range.loop, toString] at *
    · case_transition Hcontains : (Module.inputs noc_lowM), ident,
     (PortMap.getIO_not_contained_false' Hrule)
      simp only [
        noc_lowM,
        AssocList.contains_eq, AssocList.toList,
        List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq
      ] at Hcontains
      rcases Hcontains with Hident | Hident | Hident | Hident
      <;> subst ident
      <;> dsimp only [noc_lowM, drcompute] at Hrule v ⊢
      <;> exists s.concat v
      <;> simpa
    · case_transition Hcontains : (Module.outputs noc_lowM), ident,
     (PortMap.getIO_not_contained_false' Hrule)
      simp only [
        noc_lowM,
        AssocList.contains_eq, AssocList.toList,
        List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq
      ] at Hcontains
      rcases Hcontains with Hident | Hident | Hident | Hident
      <;> subst ident
      <;> dsimp only [noc_lowM, drcompute] at Hrule v ⊢
      <;> unfold φ at H
      · obtain ⟨⟨Hrule1, Hrule2⟩, Hrule3⟩ := Hrule
        rw [Hrule1] at H
        obtain ⟨i, Hi⟩ := perm_in_perm_l (H := H) (v := v)
        exists List.eraseIdx s ↑i
        and_intros
        · apply arbiterXY_correct at Hrule2; rw [Hrule2]
        · exists i; rw [←Hi]; simpa
      · obtain ⟨⟨⟨Hrule1, Hrule2⟩, Hrule3⟩, Hrule4⟩ := Hrule
        rw [Hrule1] at H
        obtain ⟨i, Hi⟩ := perm_in_perm_l (H := H) (v := v)
        exists List.eraseIdx s ↑i
        and_intros
        · apply arbiterXY_correct at Hrule2; rw [Hrule2]
        · exists i; rw [←Hi]; simpa
      · obtain ⟨⟨⟨⟨Hrule1, Hrule2⟩, Hrule3⟩, Hrule4⟩, Hrule5⟩ := Hrule
        rw [Hrule1] at H
        obtain ⟨i, Hi⟩ := perm_in_perm_l (H := H) (v := v)
        exists List.eraseIdx s ↑i
        and_intros
        · apply arbiterXY_correct at Hrule2; rw [Hrule2]
        · exists i; rw [←Hi]; simpa
      · obtain ⟨⟨⟨⟨Hrule1, Hrule2⟩, Hrule3⟩, Hrule4⟩, Hrule5⟩ := Hrule
        rw [Hrule1] at H
        obtain ⟨i, Hi⟩ := perm_in_perm_l (H := H) (v := v)
        exists List.eraseIdx s ↑i
        and_intros
        · apply arbiterXY_correct at Hrule2; rw [Hrule2]
        · exists i; rw [←Hi]; simpa

theorem noc_low_correct : noc_lowM ⊑ noc := by
  apply (
    Module.refines_φ_refines
      noc_low_ϕ_indistinguishable
      noc_low_refines_initial
      noc_low_refines_φ
  )

end DataflowRewriter.Examples.NoC
