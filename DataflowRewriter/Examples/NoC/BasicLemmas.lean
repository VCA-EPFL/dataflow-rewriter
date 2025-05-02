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

open Batteries (AssocList)

namespace DataflowRewriter.Examples.NoC

-- TODO: This should be moved elsewhere at some point

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

theorem isSome_same_AssocList {α β} [DecidableEq α] {y : α} {l1 l2 : AssocList α β} :
  (∀ x, l1.contains x <-> l2.contains x) →
  (l1.find? y).isSome = (l2.find? y).isSome := by
    sorry

theorem eraseIdx_len {T} {l1 l2 : List T} {i} (Hlen : i < List.length l1):
  List.eraseIdx (l1 ++ l2) i = (List.eraseIdx l1 i) ++ l2 := by
    revert l2
    revert i
    induction l1
    · intros; contradiction
    · intros i; induction i <;> try simpa
      intros Hlen l2
      simp only [List.length_cons, add_lt_add_iff_right] at Hlen
      rename_i _ _ H3 _ _
      simpa [H3 Hlen]

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
  (Heq : f i = v := by rfl) (Hlt : i < sz := by simpa) :
  PortMap.getIO
    (List.map
      (λ n => ⟨(NatModule.stringify_input n: InternalPort String), f n⟩)
      (List.range sz)
    ).toAssocList
    (NatModule.stringify_input i)
  = v := by
    sorry

theorem getIO_map_range {S : Type _} {Ident} [DecidableEq Ident]
  {f : Nat -> InternalPort Ident} {Hinj : Function.Injective f}
  {g : Nat -> Σ T : Type _, (S → T → S → Prop)}
  {i : Nat} {sz : Nat} {v}
  (Heq : g i = v := by rfl) (Hlt : i < sz := by simpa) :
  PortMap.getIO (List.map (λ n => ⟨f n, g n⟩) (List.range sz)).toAssocList (f i)
  = v := by
    sorry

theorem getIO_map_stringify_output {S : Type _}
  {i : Nat} {sz : Nat}
  {f : Nat -> Σ T : Type _, (S → T → S → Prop)} {v}
  (Heq : f i = v := by rfl) (Hlt : i < sz := by simpa) :
  PortMap.getIO
    (List.map
      (λ n => ⟨(NatModule.stringify_output n: InternalPort String), f n⟩)
      (List.range sz)
    ).toAssocList
    (NatModule.stringify_output i)
  = v := by
    -- FIXME: Induction on List.range is still problematic
    sorry

theorem getIO_map_ident {Ident} [DecidableEq Ident] {S : Type _}
  {ident : InternalPort Ident} {sz : Nat}
  {f : Nat → InternalPort Ident}
  {g : Nat -> Σ T : Type _, (S → T → S → Prop)} {init_i v new_i}:
  (PortMap.getIO
    (List.map (λ n => ⟨f n, g n⟩) (List.range sz)).toAssocList
    ident
  ).snd init_i v new_i
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

theorem stringify_input_inj :
  Function.Injective NatModule.stringify_input := by
    sorry

theorem stringify_input_neq {n1 n2 : Nat} (Hneq : n1 ≠ n2) :
  NatModule.stringify_input n1 ≠ NatModule.stringify_input n2
    := by
      intros H; apply stringify_input_inj at H; contradiction

theorem stringify_output_inj :
  Function.Injective NatModule.stringify_output := by
    sorry

theorem stringify_output_neq {n1 n2 : Nat} (Hneq : n1 ≠ n2) :
  NatModule.stringify_output n1 ≠ NatModule.stringify_output n2
    := by
      intros H; apply stringify_output_inj at H; contradiction

theorem internalport_neq {ident1 ident2 : InstIdent String} {name1 name2 : String}
  (Hneq : name1 ≠ name2) :
    ({ inst := ident1, name := name1 }: InternalPort String)
  ≠ ({ inst := ident2, name := name2 }: InternalPort String)
    := by simpa [Hneq]

end DataflowRewriter.Examples.NoC
