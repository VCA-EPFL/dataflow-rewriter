/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import Lean
import Init.Data.BitVec.Lemmas
import Qq

import DataflowRewriter.Simp
import DataflowRewriter.Module
import DataflowRewriter.ExprLow
import DataflowRewriter.ExprLowLemmas
import DataflowRewriter.Component
import DataflowRewriter.KernelRefl
import DataflowRewriter.Reduce
import DataflowRewriter.List
import DataflowRewriter.Tactic
import DataflowRewriter.AssocList
import DataflowRewriter.Examples.NoC.Basic
import DataflowRewriter.Examples.NoC.Components

open Batteries (AssocList)

namespace DataflowRewriter.NoC

variable [P: NocParam]

attribute [drcompute] Batteries.AssocList.toList Function.uncurry Module.mapIdent
  List.toAssocList List.foldl Option.pure_def Option.bind_eq_bind Option.bind_some
  Module.renamePorts Batteries.AssocList.mapKey InternalPort.map Nat.repr
  Nat.toDigits Nat.toDigitsCore Nat.digitChar List.asString Option.bind
  Batteries.AssocList.mapVal beq_self_eq_true
  Option.getD cond beq_self_eq_true beq_iff_eq  InternalPort.mk.injEq
  String.reduceEq and_false imp_self BEq.beq AssocList.bijectivePortRenaming
  AssocList.keysList List.inter AssocList.filterId
  AssocList.append AssocList.filter

attribute [drdecide] InternalPort.mk.injEq and_false decide_False decide_True
  and_true Batteries.AssocList.eraseAllP  InternalPort.mk.injEq
  and_false decide_False decide_True reduceCtorEq cond List.map List.elem_eq_mem
  List.mem_cons List.mem_singleton Bool.decide_or InternalPort.mk.injEq
  String.reduceEq and_false decide_false reduceCtorEq and_self Bool.or_self
  Bool.false_eq_true not_false_eq_true List.filter_cons_of_neg and_true
  List.filter_nil List.empty_eq decide_true List.nodup_cons List.not_mem_nil
  List.nodup_nil Bool.and_self reduceIte List.concat_eq_append dreduceIte
  List.append_nil

-- TODO: This file is starting to get big.
-- We should split every implementation (And proof of correctness) into their
-- own file

-- NBag Implementation ---------------------------------------------------------

def ε_nbag : Env :=
  [
    (s!"Merge' {P.DataS} {P.netsz}", ⟨_, StringModule.merge' P.Data P.netsz⟩),
    (s!"Bag {P.DataS}", ⟨_, StringModule.bag P.Data⟩),
  ].toAssocList

def ε_nbag_merge' :
  ε_nbag.find? s!"Merge' {P.DataS} {P.netsz}" = .some ⟨_, StringModule.merge' P.Data P.netsz⟩ := by
  simpa

def ε_nbag_bag :
  ε_nbag.find? s!"Bag {P.DataS}" = .some ⟨_, StringModule.bag P.Data⟩ := by
    sorry

def nbag_low : ExprLow String :=
  let merge := ExprLow.base
    {
      input := List.range P.netsz |>.map (λ i => ⟨
        -- Port defined in the Type (Must have inst := InstIdent.top)
        NatModule.stringify_input i,
        -- Internal name, here a top level port
        NatModule.stringify_input i,
      ⟩) |>.toAssocList,
      output := [⟨
        -- Port defined in the Type (Must have inst := InstIdent.top)
        NatModule.stringify_output 0,
        -- Internal name
        { inst := InstIdent.internal "Merge", name := "merge_to_bag_out" }
      ⟩].toAssocList,
    }
    s!"Merge' {P.DataS} {P.netsz}" -- Instance Type
  let bag := ExprLow.base
    {
      input := [⟨
        NatModule.stringify_input 0,
        { inst := InstIdent.internal "Bag", name := "merge_to_bag_in" }
      ⟩].toAssocList,
      output := [⟨
        NatModule.stringify_output 0,
        NatModule.stringify_output 0
      ⟩].toAssocList,
    }
    s!"Bag {P.DataS}" -- Instance Type
  ExprLow.connect
    {
      output  := { inst := InstIdent.internal "Merge",  name := "merge_to_bag_out"  },
      input   := { inst := InstIdent.internal "Bag",    name := "merge_to_bag_in"   },
    }
    (ExprLow.product bag merge)

def nbag_lowT : Type := by
  precomputeTac [T| nbag_low, ε_nbag] by
    simp [drunfold, seval, drdecide, -AssocList.find?_eq]
    rw [ε_nbag_merge', ε_nbag_bag]
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,-AssocList.mapKey_mapKey]

def nbag_lowM : StringModule nbag_lowT := by
  precomputeTac [e| nbag_low, ε_nbag] by
    simp [drunfold, seval, drdecide, -AssocList.find?_eq]
    rw [ε_nbag_merge', ε_nbag_bag]
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq]
    conv =>
      pattern (occs := *) Module.connect'' _ _
      all_goals
        rw [(Module.connect''_dep_rw (h := by simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?]; rfl)
                                     (h' := by simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?]; rfl))]; rfl
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?,AssocList.filter,-Prod.exists]
    unfold Module.connect''
    simp
    simp [AssocList.mapKey_mapKey, AssocList.mapVal_mapKey]
    simp [AssocList.mapVal_map_toAssocList]
    simp [AssocList.mapKey_map_toAssocList]
    simp [AssocList.bijectivePortRenaming_same]
    simp [InternalPort.map]
    have Hneq: ∀ x,
      ({ inst := InstIdent.top, name := NatModule.stringify_input x }: InternalPort String)
      ≠ ({ inst := InstIdent.internal "Bag", name := "merge_to_bag_in" }: InternalPort String)
    · simpa
    simp [AssocList.eraseAll_map_neq (Hneq := Hneq)]
    simp [AssocList.eraseAll]
    simp [Module.liftR]

-- NBranch Implementation ------------------------------------------------------
-- TODO

-- NRoute Implementation -------------------------------------------------------

def ε_nroute : Env :=
  [
    (s!"Split {P.DataS} {FlitHeaderS}", ⟨_, StringModule.split P.Data FlitHeader⟩),
    (s!"NBranch {P.DataS} {P.netsz}", ⟨_, StringModule.bag P.Data⟩),
  ].toAssocList

def ε_nroute_split :
  ε_nroute.find? s!"Split {P.DataS} {FlitHeaderS}" = .some ⟨_, StringModule.split P.Data FlitHeader⟩ := by
  simpa

def ε_nroute_nbranch :
  ε_nroute.find? s!"NBranch {P.DataS} {P.netsz}" = .some ⟨_, nroute⟩ := by
    sorry

def nroute_low : ExprLow String :=
  let split := ExprLow.base
    {
      input := [
        ⟨NatModule.stringify_input 0, NatModule.stringify_input 0⟩
      ].toAssocList,
      output := [
        ⟨
          NatModule.stringify_output 0,
          { inst := InstIdent.internal "Split", name := NatModule.stringify_output 0 }
        ⟩,
        ⟨
          NatModule.stringify_output 1,
          { inst := InstIdent.internal "Split", name := NatModule.stringify_output 1 }
        ⟩
      ].toAssocList,
    }
    s!"Split {P.DataS} {FlitHeaderS}"
  let nbranch := ExprLow.base
    {
      input := [
        ⟨
          NatModule.stringify_input 0,
          { inst := InstIdent.internal "NBranch", name := NatModule.stringify_input 0 }
        ⟩,
        ⟨
          NatModule.stringify_input 1,
          { inst := InstIdent.internal "NBranch", name := NatModule.stringify_input 1 }
        ⟩,
      ].toAssocList,
      output := List.range P.netsz |>.map (λ i => ⟨
        NatModule.stringify_output i,
        NatModule.stringify_output i,
      ⟩) |>.toAssocList,
    }
    s!"NBranch {P.DataS} {P.netsz}"
  let connection (i : Nat) : Connection String :=
    {
      output := {
        inst := InstIdent.internal "Split",
        name := NatModule.stringify_output i
      },
      input := {
        inst := InstIdent.internal "NBranch",
        name := NatModule.stringify_input i
      },
    }
  ExprLow.product split nbranch
  |> ExprLow.connect (connection 0)
  |> ExprLow.connect (connection 1)

def nroute_lowT : Type := by
  precomputeTac [T| nroute_low, ε_nroute] by
    simp [drunfold, seval, drdecide, -AssocList.find?_eq]
    rw [ε_nroute_split, ε_nroute_nbranch]
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,-AssocList.mapKey_mapKey]

def nroute_lowM : StringModule nroute_lowT := by
  precomputeTac [e| nroute_low, ε_nroute] by
    simp [drunfold, seval, drdecide, -AssocList.find?_eq]
    rw [ε_nroute_split, ε_nroute_nbranch]
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq]
    conv =>
      pattern (occs := *) Module.connect'' _ _
      all_goals
        rw [(Module.connect''_dep_rw (h := by simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?]; rfl)
                                     (h' := by simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?]; rfl))]; rfl
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?,AssocList.filter,-Prod.exists]
    unfold Module.connect''
    simp
    simp [AssocList.mapKey_mapKey, AssocList.mapVal_mapKey]
    simp [AssocList.mapVal_map_toAssocList]
    simp [AssocList.mapKey_map_toAssocList]
    simp [AssocList.bijectivePortRenaming_same]
    simp [InternalPort.map]
    -- TODO:
    -- have Hneq: ∀ x,
    --   ({ inst := InstIdent.top, name := NatModule.stringify_input x }: InternalPort String)
    --   ≠ ({ inst := InstIdent.internal "Bag", name := "merge_to_bag_in" }: InternalPort String)
    -- · simpa
    -- simp [AssocList.eraseAll_map_neq (Hneq := Hneq)]
    -- simp [AssocList.eraseAll]
    -- simp [Module.liftR]

-- Useful lemmas ---------------------------------------------------------------
-- TODO: This should maybe be moved somewhere else

theorem some_isSome {α} {f : α → Bool} {l : List α} v :
  List.find? f l = some v -> (List.find? f l).isSome := by
    intros H; simpa [H, Option.isSome_some]

theorem none_isSome {α} {f : α → Bool} {l : List α} :
  List.find? f l = none -> (List.find? f l).isSome = false := by
    intros H; simpa [H, Option.isSome_none]

theorem isSome_same_list {α} {f : α → Bool} {g : α → Bool} {l : List α} :
  ((∃ x, x ∈ l ∧ f x) <-> (∃ x, x ∈ l ∧ g x)) →
  (List.find? f l).isSome = (List.find? g l).isSome := by
    intros H
    obtain ⟨H1, H2⟩ := H
    cases Hf: (List.find? f l) <;> cases Hg: (List.find? g l) <;> try simpa
    · apply some_isSome at Hg; rw [List.find?_isSome] at Hg
      apply H2 at Hg; rw [←List.find?_isSome] at Hg
      rw [Hf] at Hg
      contradiction
    · apply some_isSome at Hf; rw [List.find?_isSome] at Hf
      apply H1 at Hf; rw [←List.find?_isSome] at Hf
      rw [Hg] at Hf
      contradiction

theorem eraseIdx_len {T} {l1 l2 : List T} {i} (H : i < List.length l1):
  List.eraseIdx (l1 ++ l2) i = (List.eraseIdx l1 i) ++ l2 := by
    sorry

theorem get_len {T} (l1 l2: List T) i
  (H1 : i < List.length l1)
  (H2 : i < List.length (l1 ++ l2) := by simpa [Nat.lt_add_right]):
  l1[i] = (l1 ++ l2)[i] := by
    revert H1 H2 i
    induction l1 <;> intros i <;> induction i <;> simp <;> try contradiction
    intros H1 H2
    rename_i hd tl HR1 n HR2
    apply HR1

-- TODO: This could be generalized, but it is a bit tricky to keep correct
-- The two version should suffice for simple use cases
theorem getIO_map_stringify_input {S : Type _}
  {i : Nat} {sz : Nat}
  {f : Nat -> Σ T : Type _, (S → T → S → Prop)} {v}
  (Heq : f i = v) (Hlt : i < sz) :
  PortMap.getIO (List.range sz |>.map
    (λ n => ⟨(NatModule.stringify_input n: InternalPort String), f n⟩) |>.toAssocList)
    (NatModule.stringify_input i) = v := by
  sorry

theorem getIO_map_stringify_output {S : Type _}
  {i : Nat} {sz : Nat}
  {f : Nat -> Σ T : Type _, (S → T → S → Prop)} {v}
  {Heq : f i = v} {Hlt : i < sz} :
  PortMap.getIO (List.range sz |>.map
    (λ n => ⟨(NatModule.stringify_output n: InternalPort String), f n⟩) |>.toAssocList)
    (NatModule.stringify_output i) = v := by
    -- FIXME: Induction on List.range is still problematic
  sorry

theorem getIO_map_ident {Ident} [DecidableEq Ident] {S : Type _}
  {ident : InternalPort Ident} {sz : Nat}
  {f : Nat → InternalPort Ident}
  {g : Nat -> Σ T : Type _, (S → T → S → Prop)} {init_i v new_i}:
  (PortMap.getIO (List.range sz |>.map (λ n => ⟨f n, g n⟩) |>.toAssocList) ident).snd
    init_i v new_i
  → ∃ n, n < sz ∧ ident = f n := by
    -- FIXME: Induction on List.range is still problematic
    sorry

theorem getIO_map_ident_match_1 {Ident} [DecidableEq Ident] {S1 S2 : Type _}
  {ident : InternalPort Ident} {sz : Nat}
  {f : Nat → InternalPort Ident}
  {g1 : Nat -> Σ T : Type _, (S1 → T → S1 → Prop)}
  {g2 : Nat -> Σ T : Type _, (S2 → T → S2 → Prop)}
  (Heq : ∀ n, (g1 n).1 = (g2 n).1):
  (PortMap.getIO (List.map (λ n => ⟨f n, g1 n⟩) (List.range sz)).toAssocList ident).fst =
  (PortMap.getIO (List.map (λ n => ⟨f n, g2 n⟩) (List.range sz)).toAssocList ident).fst :=
  by
    -- FIXME: Induction on List.range is still problematic
    sorry

-- Correctness of nbag implementation ------------------------------------------
-- TODO: We are currently only trying to prove a refinement in one way, but it
-- would be nice to have a proof of equivalence instead

instance : MatchInterface nbag_lowM (nbag P.Data P.netsz) where
  input_types := by
    intros ident
    unfold nbag_lowM nbag nbag'
    unfold lift_f mk_nbag_input_rule
    simp [NatModule.stringify, Module.mapIdent, InternalPort.map, NatModule.stringify_output] at *
    simp [AssocList.mapKey_map_toAssocList, InternalPort.map]
    apply (getIO_map_ident_match_1 (Heq := by intros n; simpa))
  output_types := by
    intros ident
    unfold nbag_lowM nbag nbag'
    dsimp
    by_cases H: ({ inst := InstIdent.top, name := NatModule.stringify_output 0 }: InternalPort String) = ident
    <;> simp [*, drunfold, drnat, PortMap.getIO_cons, NatModule.stringify_output, InternalPort.map] at *
    <;> simpa [*]
  inputs_present := by
    intros ident
    unfold nbag_lowM nbag nbag'
    simp [NatModule.stringify, Module.mapIdent]
    apply isSome_same_list
    constructor <;> intros H <;> obtain ⟨x, Hx1, Hx2⟩ := H <;> simp at * <;> exists x
  outputs_present := by
    intros ident;
    unfold nbag_lowM nbag nbag'
    by_cases H: ({ inst := InstIdent.top, name := NatModule.stringify_output 0 }: InternalPort String) = ident
    <;> simp [*, drunfold, drnat, PortMap.getIO_cons, NatModule.stringify_output, InternalPort.map] at *
    <;> simpa [*]

def φ (I : nbag_lowT) (S : List P.Data) : Prop :=
  S = I.fst ++ I.snd

theorem nbag_low_correctϕ : nbag_lowM ⊑_{φ} (nbag P.Data P.netsz) := by
  intros i s H
  constructor
  · intro ident mid_i v Hrule
    case_transition Hcontains : (Module.inputs nbag_lowM), ident,
     (fun x => PortMap.getIO_not_contained_false' x Hrule)
    simp [nbag_lowM] at Hcontains
    obtain ⟨ n, HnFin, Hident ⟩ := Hcontains
    subst ident
    unfold nbag nbag'
    simp [NatModule.stringify, Module.mapIdent, InternalPort.map, NatModule.stringify_output]
    exists mid_i.1 ++ mid_i.2
    split_ands
    · unfold lift_f;
      rw [PortMap.rw_rule_execution (h := by rw[AssocList.mapKey_map_toAssocList])]
      dsimp [InternalPort.map]
      rw [PortMap.rw_rule_execution (h := by apply (getIO_map_stringify_input
          (Heq := by unfold mk_nbag_input_rule; rfl)
        ) <;> simpa)
      ]
      dsimp
      subst s
      dsimp [nbag_lowM] at v Hrule
      rw [getIO_map_stringify_input (i := n) (f := fun x => ⟨NocParam.Data, λ x ret
        (x_1 : List NocParam.Data × List NocParam.Data) => x_1.2 = x.2 ++ [ret] ∧
        x.1 = x_1.1⟩) (Heq := by rfl) (Hlt := HnFin)] at v
      rw [PortMap.rw_rule_execution
        (h := by apply (getIO_map_stringify_input
          (i := n)
          (f := fun x => ⟨NocParam.Data, λ x ret (x_1 : List NocParam.Data × List NocParam.Data) => x_1.2 = x.2 ++ [ret] ∧ x.1 = x_1.1⟩)
          (Heq := by rfl)
          (Hlt := HnFin)
        ) <;> simpa
        )
      ] at Hrule
      dsimp at Hrule v
      obtain ⟨ Hrule1, Hrule2 ⟩ := Hrule
      rw [Hrule1, ←Hrule2]
      simpa
    · exists mid_i.1 ++ mid_i.2; split_ands
      · constructor
      · rfl
  · intro ident mid_i v Hrule
    case_transition Hcontains : (Module.outputs nbag_lowM), ident,
     (fun x => PortMap.getIO_not_contained_false' x Hrule)
    simp [nbag_lowM] at Hcontains
    subst ident
    obtain ⟨⟨i_1, ⟨H1, H2⟩⟩, Hrule2⟩ := Hrule
    exists mid_i.1 ++ mid_i.2
    split_ands
    · unfold nbag nbag'
      simp [NatModule.stringify, Module.mapIdent, InternalPort.map, NatModule.stringify_output]
      rw [PortMap.rw_rule_execution]
      dsimp
      subst s
      rw [H1, H2]
      have H: (i_1: Nat) < List.length (i.1 ++ i.2) := by simpa [Nat.lt_add_right]
      exists Fin.mk i_1 H
      split_ands <;> dsimp
      · rw [Hrule2, ←eraseIdx_len] <;> simpa
      · apply get_len
    · rfl
  · intros _ mid_i _ _;
    rename_i rule H1 H2
    simp [nbag_lowM, nbag, nbag', NatModule.stringify, Module.mapIdent] at *
    rw [H1] at H2
    obtain ⟨a, b, output, ⟨⟨H2, H3⟩, H4, H5⟩⟩ := H2
    exists s
    split_ands
    · constructor
    · unfold φ at *;
      subst a b s
      rw [H4, H2]
      simpa

theorem nbag_low_ϕ_indistinguishable :
  ∀ x y, φ x y → Module.indistinguishable nbag_lowM (nbag P.Data P.netsz) x y := by
    intros x y Hϕ
    constructor
    <;> intros ident new_i v H
    <;> exists new_i.1 ++ new_i.2
    <;> unfold nbag nbag'
    <;> simp [NatModule.stringify, Module.mapIdent]
    · subst y
      unfold nbag_lowM at *
      dsimp at v H
      unfold lift_f
      rw [PortMap.rw_rule_execution (h := by rw [AssocList.mapKey_map_toAssocList])]
      dsimp [InternalPort.map]
      have ⟨ n, Hn1, Hn2 ⟩ := getIO_map_ident H
      subst ident
      rw [PortMap.rw_rule_execution
        (h := by apply (getIO_map_stringify_input (Heq := by unfold mk_nbag_input_rule; rfl)) <;> simpa)
      ]
      rw [getIO_map_stringify_input (i := n) (f := fun x => ⟨NocParam.Data, λ x ret
        (x_1 : List NocParam.Data × List NocParam.Data) => x_1.2 = x.2 ++ [ret] ∧
        x.1 = x_1.1⟩) (Heq := by rfl)] at v
      rw [PortMap.rw_rule_execution
        (h := by apply (getIO_map_stringify_input
          (i := n)
          (f := fun x => ⟨NocParam.Data, λ x ret (x_1 : List NocParam.Data × List NocParam.Data) => x_1.2 = x.2 ++ [ret] ∧ x.1 = x_1.1⟩)
          (Heq := by rfl)) <;> simpa
        )
      ] at H
      dsimp at H v
      simp
      obtain ⟨ H1, H2 ⟩ := H
      rw [H1, ←H2]
      simpa
    · by_cases Hident: ({ inst := InstIdent.top, name := NatModule.stringify_output 0 }: InternalPort String) = ident
      · rw [PortMap.rw_rule_execution] at H
        simp [NatModule.stringify_output] at *
        subst ident
        rw [PortMap.rw_rule_execution (h := by apply PortMap.getIO_cons)];
        simp at *
        obtain ⟨⟨i, Hi1, Hi2⟩, H⟩ := H
        rw [Hi1, Hi2]
        subst y
        have Hlen: (i: Nat) < List.length (x.1 ++ x.2) := by simpa [Nat.lt_add_right]
        exists Fin.mk i Hlen
        split_ands
        · rw [←eraseIdx_len] <;> simpa [H, Nat.lt_add_right]
        · apply get_len
      · exfalso
        apply (PortMap.getIO_cons_nil_false _ _ ident)
        · exact Hident
        · exact H

theorem nbag_low_correct : nbag_lowM ⊑ (nbag P.Data P.netsz) := by
  apply (Module.refines_φ_refines nbag_low_ϕ_indistinguishable nbag_low_correctϕ)

-- NoC implementation ----------------------------------------------------------

def ε_noc : Env :=
  [
    -- Empty component (Always useful)
    (s!"Empty", ⟨_, StringModule.empty⟩),

    -- Bags to receive message (One per router)
    (s!"NBag {P.DataS} {P.netsz}", ⟨_, StringModule.bag P.Data⟩),

    -- Branching for routing
    (s!"NRoute {P.DataS} {P.netsz}", ⟨_, nbranch⟩),
  ].toAssocList

def ε_noc_empty :
  ε_noc.find? s!"Empty" = .some ⟨_, StringModule.empty⟩ := by
  simpa

def ε_noc_nroute :
  ε_noc.find? s!"NRoute {P.DataS} {P.netsz}" = .some ⟨_, nroute⟩ := by sorry

def ε_noc_nbag :
  ε_noc.find? s!"NBag {P.DataS} {P.netsz}" = .some ⟨_, nbag P.Data P.netsz⟩ := by sorry

def noc_low : ExprLow String :=
  let empty : ExprLow String := ExprLow.base {} s!"Empty"
  let gadget (i : RouterID) : ExprLow String :=
    let nroute := ExprLow.base
      {
        input := [⟨
          NatModule.stringify_input 0,
          NatModule.stringify_input i,
        ⟩].toAssocList,
        output := List.range P.netsz |>.map (λ j => ⟨
          NatModule.stringify_output j,
          { inst := InstIdent.internal s!"NRoute {i}", name := NatModule.stringify_output j}
        ⟩) |>.toAssocList
      }
      s!"NRoute {P.DataS} {P.netsz}"
    let nbag : ExprLow String := ExprLow.base
      {
        input := List.range P.netsz |>.map (λ j => ⟨
          NatModule.stringify_input j,
          { inst := InstIdent.internal s!"NBag {i}", name := NatModule.stringify_input j }
        ⟩) |>.toAssocList,
        output := [⟨
          NatModule.stringify_output 0,
          NatModule.stringify_output i
        ⟩].toAssocList,
      }
      s!"NBag {P.DataS} {P.netsz}"
    ExprLow.product nbag nroute
  List.foldl (fun acc i =>
    List.foldl (fun acc j =>
      ExprLow.connect
      {
        output := { inst := InstIdent.internal s!"NRoute {i}", name := NatModule.stringify_output i },
        input := { inst := InstIdent.internal s!"NBag {i}", name := NatModule.stringify_input i },
      }
      acc
    )
    (ExprLow.product acc (gadget i))
    (List.range P.netsz)
  )
  empty
  (List.range P.netsz)

def noc_lowT : Type := by
  precomputeTac [T| noc_low, ε_noc] by
    unfold noc_low
    -- TODO

def noc_lowM : StringModule noc_lowT := by
  precomputeTac [e| noc_low, ε_noc] by
    unfold noc_low
    -- TODO

-- Correctness of NoC implementation -------------------------------------------

-- TODO

end DataflowRewriter.NoC
