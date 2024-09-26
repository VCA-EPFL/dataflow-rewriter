/-
Copyright (c) 2024 Yann Herklotz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Leanses
import Lean
import Init.Data.BitVec.Lemmas
import Qq

import DataflowRewriter.Simp
import DataflowRewriter.Module
import DataflowRewriter.Component
import DataflowRewriter.KernelRefl
import DataflowRewriter.Reduce
import DataflowRewriter.List

open Qq

open Batteries (AssocList)
open Batteries (RBMap)

open Lean.Meta Lean.Elab

namespace DataflowRewriter

def threemerge T : Module (List T):=
  { inputs := RBMap.ofList [("a", ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩),
               ("b", ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩),
               ("c", ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩)] _,
    outputs := RBMap.ofList [("z", ⟨ T, λ oldList oldElement newList => ∃ i, newList = oldList.remove i ∧ oldElement = oldList.get i ⟩)] _,
    internals := []
  }

@[simp]
def mergeLow : ExprLow :=
  let merge1 := .base "merge1" "merge"
  let merge2 := .base "merge2" "merge"
  .product merge1 merge2
  |> .connect ⟨"merge1", "z"⟩ ⟨"merge2", "a"⟩
  |> .rename ⟨"merge1", "a"⟩ "a"
  |> .rename ⟨"merge1", "b"⟩ "b"
  |> .rename ⟨"merge2", "b"⟩ "c"
  |> .rename ⟨"merge2", "z"⟩ "z"

def merge_sem (T: Type _) :=
  match build_module' mergeLow (RBMap.ofList [("merge", ⟨List T, merge T⟩)] _) with
  | some x => x
  | none => ⟨Unit, Module.empty⟩

attribute [dmod] AssocList.find? BEq.beq decide instIdentDecidableEq instDecidableEqString String.decEq RBMap.ofList RBMap.find? RBMap.findEntry? Batteries.RBSet.ofList Batteries.RBSet.insert Option.map Batteries.RBSet.findP? Batteries.RBNode.find? compare compareOfLessAndEq

theorem inputs_match {S S'} (A : Module S) (B : Module S') :
  A.inputs.toList.map (·.fst) = B.inputs.toList.map (·.fst) →
  ∀ (ident : Ident), (A.inputs.getIO ident).1 = (B.inputs.getIO ident).1 := by sorry

theorem outputs_match {S S'} (A : Module S) (B : Module S') :
  A.outputs.toList.map (·.fst) = B.outputs.toList.map (·.fst) →
  ∀ (ident : Ident), (A.outputs.getIO ident).1 = (B.outputs.getIO ident).1 := by sorry

theorem interface_match T : matching_interface ((merge_sem T).snd) (threemerge T) := by sorry

instance matching_three {T} : MatchingModules (List T × List T) (List T) where
  imod := (merge_sem T).snd
  smod := threemerge T
  matching := interface_match T

/--
Same as keysList, but is implemented in terms of toList, as there are more
lemmas avaiable for it.
-/
def _root_.Batteries.RBMap.keysList' {α β γ} (m : RBMap α β γ) := m.toList.map (·.1)

theorem keysInMap {α β γ} [@Batteries.OrientedCmp α γ] [@Batteries.TransCmp α γ] (m : RBMap α β γ) : ∀ k, k ∈ m.keysList' → m.contains k := by
  dsimp only [RBMap.contains, RBMap.keysList', Option.isSome]
  intro k H
  apply List.exists_of_mem_map at H
  rcases H with ⟨ ⟨ k, v ⟩, H, Heq ⟩; subst_vars
  have H' : m.findEntry? k = some (k, v) := by
    rw [Batteries.RBMap.findEntry?_some]
    solve_by_elim [Batteries.OrientedCmp.cmp_refl]
  simp [H']

theorem keysInMap' {α β γ} [BEq α] [LawfulBEq α] [Batteries.BEqCmp (α := α) γ] [@Batteries.TransCmp α γ] (m : RBMap α β γ) : ∀ k, m.contains k → k ∈ m.keysList' := by
  dsimp only [RBMap.contains, RBMap.keysList', Option.isSome]
  intro k H
  split at H <;> [skip ; simp at H]
  rename_i _ _ Hfind
  rw [Batteries.BEqCmp.cmp_iff_eq.mp (RBMap.findEntry?_some_eq_eq Hfind)]
  solve_by_elim [List.mem_map_of_mem, Batteries.RBMap.findEntry?_some_mem_toList]

theorem merge_sem_type {T} : Sigma.fst (merge_sem T) = (List T × List T) := by ker_refl

theorem getIO_none {S} (m : IdentMap ((T : Type) × (S → T → S → Prop))) ident :
  m.findEntry? ident = none ->
  m.getIO ident = ⟨ PUnit, λ _ _ _ => True ⟩ := by
  intros H; simp [H, IdentMap.getIO, RBMap.findD, RBMap.find?]

theorem getIO_some {S} (m : IdentMap ((T : Type) × (S → T → S → Prop))) ident t :
  m.findEntry? ident = some (ident, t) ->
  m.getIO ident = t := by
  intros H; simp [H, IdentMap.getIO, RBMap.findD, RBMap.find?]

def rule_rw {S T T'} (r : S → T → S → Prop) (eq : T = T') : S → T' → S → Prop :=
  fun a b => r a (eq.mpr b)

@[simp]
theorem input_keys T : ((@matching_three T).imod).inputs.keysList' = ["a", "b", "c"] := by ker_refl

@[simp]
theorem other {T} : ((@matching_three T).imod).inputs.getIO "a" = ⟨T, fun x ret x_1 => x_1.1 = ret :: x.1 ∧ x.2 = x_1.2⟩ := by ker_refl

@[simp]
theorem other' {T} : ((@matching_three T).smod).inputs.getIO "a" = ⟨T, fun oldList newElement newList => newList = newElement :: oldList⟩ := by ker_refl

theorem in_inputs {α β γ} [BEq α] [LawfulBEq α] [Batteries.BEqCmp (α := α) γ] [@Batteries.TransCmp α γ] (t : Batteries.RBMap α β γ) y ident : t.find? ident = some y → ident ∈ t.keysList' := by
  intro H; apply keysInMap'
  dsimp only [Batteries.RBMap.contains, Batteries.RBMap.find?, Option.map] at *
  split at H <;> cases H; simp [*]

set_option maxHeartbeats 10000 in
seal merge_sem IdentMap.getIO in
theorem correct_threeway {T: Type _} [DecidableEq T]:
    @refines _ _ (@matching_three T) (fun (x : List T × List T) y => (x.1 ++ x.2).Perm y) := by
      -- simp only [threemerge, refines]
      -- dsimp only [merge_sem_type]
      intro ⟨ x1, x2 ⟩ y HPerm indis
      -- dsimp only at HPerm
      let ⟨indisL, indisR⟩ := indis
      -- rcases indis with ⟨indisL, indisR⟩
      apply @comp_refines.mk _ _ (@matching_three T)
      . intro ident ⟨x'1, x'2⟩ v Hcontains Himod
        have := keysInMap' _ _ Hcontains
        have : ident = "a" := by sorry
        subst ident
        -- -- dsimp at this; fin_cases this
        -- ·  -- dsimp only [other, other'] at v Himod ⊢
        --   set_option trace.Meta.check true in
        --   -- set_option trace.Meta.isDefEq true in
        --   set_option trace.Meta.whnf true in
        --   -- set_option trace.Elab.match true in
        --   set_option pp.proofs true in
        clear indisL indisR Hcontains this
        simp (config := {implicitDefEqProofs := false}) only [other, other', input_keys] at v Himod
        -- simp (config := {implicitDefEqProofs := false}) only [other, other', input_keys]
        -- simp
        set_option pp.explicit true in set_option pp.proofs true in trace_state
        -- clear indisL indisR indis HPerm this Hcontains
        have : x2 = x'2 := Himod.right
        have : x'1 = v :: x1 := Himod.left
        -- rcases Himod
        let (And.intro l r) := Himod
          -- exfalso
          -- clear Hr v H hmod indis y x1 x2
          -- have t' : PUnit.{1} := Hr'.mp t -- by rw [← Hr']; exact t
          

          -- simp only [getIO_none, H] at t v ⊢
          

        -- match H : (((@matching_three T).imod).inputs.findEntry? ident) with
        -- | .some x =>
        --   unfold IdentMap.getIO RBMap.findD RBMap.find? at *
        -- | .none =>
        --   sorry
      -- · sorry
      -- · sorry
      --   sorry
      --   -- match H : (((@matching_three T).imod).inputs.findEntry? ident) with
      --   -- | some x => 
      --   --   sorry
      --   -- | none =>
      --   --   sorry
      -- · sorry
      -- · sorry
        -- (fin_cases ident <;> dsimp at *)
      --   · constructor; constructor; and_intros
      --     · rfl
      --     · apply existSR.done
      --     · rcases Hi with ⟨ Hl, Hr ⟩
      --       rw [Hl]; subst x2
      --       simp [*]
      --     · constructor <;> dsimp only
      --       · intro ident' new_i v_1 Hrule
      --         fin_cases ident' <;> simp
      --       · intros ident' new_i v_1 HVal
      --         fin_cases ident'; simp
      --         reduce at *
      --         rcases Hi with ⟨ Hil, Hir ⟩
      --         rcases HVal with ⟨ ⟨ i, HVall, temp ⟩, HValr ⟩
      --         subst x2; subst v_1
      --         generalize h : mid_i.2.get i = y'
      --         have Ht : ∃ i, mid_i.2.get i = y' := by exists i
      --         rw [← List.mem_iff_get] at Ht
      --         have Hiff := List.Perm.mem_iff (a := y') He
      --         have Ht' : y' ∈ y := by rw [← Hiff]; simp; tauto
      --         rw [List.mem_iff_get] at Ht'
      --         rcases Ht' with ⟨ i', Ht'r ⟩
      --         constructor; exists i' + 1
      --         simp; tauto
      --   · constructor; constructor; and_intros
      --     · rfl
      --     · apply existSR.done
      --     · rcases Hi with ⟨ Hl, Hr ⟩
      --       rw [Hl]; subst x2
      --       simp [*]
      --     · constructor
      --       · intros ident' new_i v_1 Hrule
      --         fin_cases ident' <;> simp
      --       · intros ident' new_i v_1 HVal
      --         fin_cases ident'; simp
      --         reduce at *
      --         rcases Hi with ⟨ Hil, Hir ⟩
      --         rcases HVal with ⟨ ⟨ i, HVall, temp ⟩, HValr ⟩
      --         subst x2; subst v_1
      --         generalize h : mid_i.2.get i = y'
      --         have Ht : ∃ i, mid_i.2.get i = y' := by exists i
      --         rw [← List.mem_iff_get] at Ht
      --         have Hiff := List.Perm.mem_iff (a := y') He
      --         have Ht' : y' ∈ y := by rw [← Hiff]; simp; tauto
      --         rw [List.mem_iff_get] at Ht'
      --         rcases Ht' with ⟨ i', Ht'r ⟩
      --         constructor; exists i' + 1
      --         simp; tauto
      --   · constructor; constructor; and_intros
      --     · rfl
      --     · apply existSR.done
      --     · rcases Hi with ⟨ Hl, Hr ⟩
      --       rw [Hl]; subst x1
      --       rw [List.perm_comm]
      --       apply List.perm_cons_append_cons; rw [List.perm_comm]; assumption
      --     · constructor
      --       · intros ident' new_i v_1 Hrule
      --         fin_cases ident' <;> simp
      --       · intros ident' new_i v_1 HVal
      --         fin_cases ident'; simp
      --         reduce at *
      --         rcases Hi with ⟨ Hil, Hir ⟩
      --         rcases HVal with ⟨ ⟨ i, HVall, temp ⟩, HValr ⟩
      --         subst x1; subst v_1
      --         generalize h : mid_i.2.get i = y'
      --         have Ht : ∃ i', mid_i.2.get i' = y' := by exists i
      --         rw [← List.mem_iff_get] at Ht
      --         -- FAILS???: rw [Hil] at Ht
      --         have Ht' : y' ∈ v :: x2 := by rw [← Hil]; assumption
      --         rcases Ht' with _ | Ht'
      --         · constructor; exists 0
      --         · rename_i Ht';
      --           have Hiff := List.Perm.mem_iff (a := y') He
      --           have : y' ∈ y := by rw [← Hiff]; simp; tauto
      --           rw [List.mem_iff_get] at this
      --           rcases this with ⟨ i, Hl ⟩
      --           constructor; exists i + 1
      --           simp; tauto
      -- . intro ident mid_i v Hi
      --   fin_cases ident <;> dsimp only at * <;> reduce at *
      --   rcases Hi with ⟨ ⟨ i, Hil ⟩, Hir ⟩
      --   reduce at *
      --   rcases Hil with ⟨ Hill, Hilr ⟩
      --   subst v; subst x1
      --   generalize Hx2get : x2.get i = v'
      --   have Hx2in : v' ∈ x2 := by rw [List.mem_iff_get]; tauto
      --   have Hiff := List.Perm.mem_iff (a := v') He
      --   have Hyin : v' ∈ y := by rw [← Hiff]; simp; tauto
      --   rw [List.mem_iff_get] at Hyin
      --   rcases Hyin with ⟨ i', Hyget ⟩
      --   have HerasePerm : (mid_i.1.append mid_i.2).Perm (y.eraseIdx i'.1) := by
      --     simp [Hill]
      --     trans; apply List.perm_append_comm
      --     rw [←List.eraseIdx_append_of_lt_length] <;> [skip; apply i.isLt]
      --     trans ((x2 ++ mid_i.1).erase x2[i])
      --     have H2 : x2[i] = (x2 ++ mid_i.1)[i] := by
      --       symm; apply List.getElem_append_left
      --     rw [H2]; symm; apply List.erase_get
      --     symm; trans; symm; apply List.erase_get
      --     rw [Hyget]; simp at Hx2get; simp; rw [Hx2get]
      --     apply List.perm_erase; symm
      --     symm; trans; symm; assumption
      --     apply List.perm_append_comm
      --   constructor; constructor; and_intros
      --   · exists i'; and_intros; rfl; tauto
      --   · apply existSR.done
      --   · assumption
      --   · constructor <;> dsimp only
      --     · intro ident' new_i v_1 Hrule
      --       fin_cases ident' <;> simp
      --     · intros ident' new_i v_1 HVal
      --       fin_cases ident'
      --       reduce at *
      --       rcases HVal with ⟨ ⟨ i'', HVall, temp ⟩, HValr ⟩
      --       subst v'; subst v_1
      --       dsimp at *
      --       have : mid_i.2[i''] ∈ (x2.eraseIdx i.1) := by
      --         simp [Hill]; apply List.getElem_mem
      --       have : mid_i.2[i''] ∈ (mid_i.1 ++ x2.eraseIdx i.1) := by
      --         rw [List.mem_eraseIdx_iff_getElem] at this; simp; right
      --         simp at *; simp [Hill]; apply List.getElem_mem
      --       have HPermIn : mid_i.2[i''] ∈ y.eraseIdx i' := by
      --         rw [List.Perm.mem_iff]; assumption; symm
      --         rw [←Hill]; assumption
      --       rw [List.mem_iff_getElem] at HPermIn
      --       rcases HPermIn with ⟨ Ha, Hb, Hc ⟩
      --       constructor; exists ⟨ Ha, Hb ⟩; tauto
      -- · intro ident mid_i Hv
      --   fin_cases ident
      --   rcases Hv with ⟨ la, lb, vout, ⟨ ⟨ i, H2, H3 ⟩, Hx3 ⟩, ⟨ Hx2, H4 ⟩ ⟩; subst lb; subst la; subst vout
      --   constructor; and_intros
      --   · apply existSR.done
      --   · rw [Hx2,← H4,←List.eraseIdx_append_of_lt_length] <;> [skip; apply i.isLt]
      --     dsimp only;
      --     trans ((x1 ++ x1[i] :: x2).erase x1[i])
      --     rw [List.perm_comm]
      --     have : x1[↑i] = x1.get i := by simp
      --     simp [*] at *
      --     have H : x1[↑i] = (x1 ++ x1[↑i] :: x2)[↑i] := by
      --       symm; apply List.getElem_append_left
      --     dsimp at *; conv => arg 1; arg 2; rw [H]
      --     apply List.erase_get
      --     trans ((x1[i] :: (x1 ++ x2)).erase x1[i])
      --     apply List.perm_erase; simp
      --     rw [List.erase_cons_head]; assumption
      --   · constructor
      --     · intros ident' new_i v_1 Hrule
      --       fin_cases ident' <;> simp
      --     · intros ident' new_i v_1 HVal
      --       fin_cases ident'
      --       reduce at *
      --       rcases HVal with ⟨ ⟨ i', _, temp ⟩, _ ⟩
      --       subst v_1
      --       generalize h : mid_i.2.get i' = y'
      --       have Ht : ∃ i', mid_i.2.get i' = y' := by exists i'
      --       rw [← List.mem_iff_get] at Ht
      --       have Hiff := List.Perm.mem_iff (a := y') He
      --       have Ht'' : y' ∈ x1.get i :: x2 := by rw [←Hx2]; assumption
      --       simp at Ht''; rcases Ht'' with (Ht'' | Ht'')
      --       · have Ht' : y' ∈ y := by
      --           rw [List.Perm.mem_iff]; rotate_left; rewrite [List.perm_comm]; assumption; subst y'
      --           rw [Ht'']; simp; left; apply List.getElem_mem
      --         dsimp; apply List.getElem_of_mem at Ht'; rcases Ht' with ⟨ Ha, Hb, Hc ⟩
      --         constructor; exists ⟨ Ha, Hb ⟩; and_intros; rfl; symm; assumption
      --       · have Ht' : y' ∈ y := by
      --           rw [List.Perm.mem_iff]; rotate_left; rewrite [List.perm_comm]; assumption; subst y'
      --           simp; tauto
      --         dsimp; apply List.getElem_of_mem at Ht'; rcases Ht' with ⟨ Ha, Hb, Hc ⟩
      --         constructor; exists ⟨ Ha, Hb ⟩; and_intros; rfl; symm; assumption

end DataflowRewriter
