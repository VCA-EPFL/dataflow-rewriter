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

abbrev Ident := Nat

elab "precompute " t:term : tactic => Tactic.withMainContext do
  let expr ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsUsingDefault
  let expr ← Lean.instantiateMVars expr
  let expr ←
    -- withTransparency .all <|
      reallyReduce (skipArgs := false) (skipTypes := false) expr
  (← Tactic.getMainGoal).assign expr

#eval show Term.TermElabM Unit from do 
  let expr ← Lean.instantiateMVars <| ← (Term.elabTerm (← `([(1:Nat) + 1, (2:Nat) + 3])) none)
  -- let res ← withTransparency .all <| Lean.ofExceptKernelException <| Lean.Kernel.whnf (← Lean.getEnv) {} expr
  let res ← reduce expr
  Lean.logInfo m!"{res}"

example : toString (1 : Nat) = "1" := by rfl

#eval show Term.TermElabM Unit from do 
  let expr ← (Term.elabTerm (← `(myCast ({ inst := "merge2", name := "a" } : InternalPort))) none)
  let res ← withTransparency .all <| Lean.ofExceptKernelException <| Lean.Kernel.whnf (← Lean.getEnv) {} expr
  -- let res ← withTransparency .all <| whnf expr
  Lean.logInfo m!"{res}"

-- example : toString ({ inst := "merge2", name := "a" } : InternalPort) = "merge2.a" := by 
--   rreduce

def threemerge T : NModule (List T):=
  { inputs := [(0, ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩),
               (1, ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩),
               (2, ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩)].toAssocList,
    outputs := [(0, ⟨ T, λ oldList oldElement newList => ∃ i, newList = oldList.remove i ∧ oldElement = oldList.get i ⟩)].toAssocList,
    internals := [λ a b => 1 + 1 = 2]
  }

seal _root_.List.get _root_.List.remove in
def threemerge' (T:Type) : NModule (List T) := by precompute threemerge T

#print threemerge'

opaque threemerge_threemerge' T : threemerge T = threemerge' T := by rfl

@[simp]
def mergeLow : ExprLow Nat :=
  let merge1 := .base 1 0
  let merge2 := .base 2 0
  .product merge1 merge2
  |> .connect ⟨1, 0⟩ ⟨2, 0⟩
  |> .input ⟨1, 0⟩ 0
  |> .input ⟨1, 1⟩ 1
  |> .input ⟨2, 1⟩ 2
  |> .output ⟨2, 0⟩ 0

def merge_sem (T: Type _) :=
  match build_module' mergeLow ([(0, ⟨List T, merge T⟩)].toAssocList) with
  | some x => x
  | none => ⟨Unit, Module.empty⟩

seal List.get List.remove in
def merge_sem' (T:Type) : ((X:Type) × NModule X) := by precompute merge_sem T

attribute [dmod] AssocList.find? BEq.beq decide instDecidableEqString String.decEq RBMap.ofList RBMap.find? RBMap.findEntry? Batteries.RBSet.ofList Batteries.RBSet.insert Option.map Batteries.RBSet.findP? Batteries.RBNode.find? compare compareOfLessAndEq

-- example T Y : merge_sem T = Y := by  

#print merge_sem'

opaque merge_sem_merge_sem' T : merge_sem T = merge_sem' T := by rfl

theorem inputs_match {S S'} (A : NModule S) (B : NModule S') :
  A.inputs.toList.map (·.fst) = B.inputs.toList.map (·.fst) →
  ∀ (ident : Ident), (A.inputs.getIO ident).1 = (B.inputs.getIO ident).1 := by sorry

theorem outputs_match {S S'} (A : NModule S) (B : NModule S') :
  A.outputs.toList.map (·.fst) = B.outputs.toList.map (·.fst) →
  ∀ (ident : Ident), (A.outputs.getIO ident).1 = (B.outputs.getIO ident).1 := by sorry

theorem interface_match T : matching_interface ((merge_sem' T).snd) (threemerge' T) := by sorry

instance matching_three {T} : MatchingModules (List T × List T) (List T) Ident where
  imod := (merge_sem' T).snd
  smod := threemerge' T
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

theorem keysInMap'' {α β} [BEq α] (m : AssocList α β) : ∀ k, m.contains k → k ∈ m.keysList := by sorry

theorem merge_sem_type {T} : Sigma.fst (merge_sem T) = (List T × List T) := by ker_refl

theorem getIO_none {S} (m : PortMap Ident ((T : Type) × (S → T → S → Prop))) (ident : Ident) :
  m.find? ↑ident = none ->
  m.getIO ident = ⟨ PUnit, λ _ _ _ => True ⟩ := by
  intros H; rw [Batteries.AssocList.find?_eq] at H
  dsimp at H; simp [H]

theorem getIO_some {S} (m : PortMap Ident ((T : Type) × (S → T → S → Prop))) (ident : Ident) t :
  m.find? ↑ident = some t ->
  m.getIO ident = t := by
  intros H; rw [Batteries.AssocList.find?_eq] at H
  dsimp at H; simp [H]

def rule_rw {S T T'} (r : S → T → S → Prop) (eq : T = T') : S → T' → S → Prop :=
  fun a b => r a (eq.mpr b)

@[simp]
theorem input_keys T : ((@matching_three T).imod).inputs.keysList = [2, 0, 1] := by rfl

@[simp]
theorem other {T} ident (h : ident ≠ 2) (h' : ((@matching_three T).imod).inputs.contains ↑ident) : ((@matching_three T).imod).inputs.getIO ident = ⟨T, fun x ret x_1 => x_1.1 = ret :: x.1 ∧ x.2 = x_1.2⟩ := by
  simp at h'
  rcases h' with h' | h' | h' <;> subst_vars <;> try rfl
  simp at h

@[simp]
theorem other' {T} : ((@matching_three T).smod).inputs.getIO 0 = ⟨T, fun oldList newElement newList => newList = newElement :: oldList⟩ := by rfl

theorem in_inputs {α β γ} [BEq α] [LawfulBEq α] [Batteries.BEqCmp (α := α) γ] [@Batteries.TransCmp α γ] (t : Batteries.RBMap α β γ) y ident : t.find? ident = some y → ident ∈ t.keysList' := by
  intro H; apply keysInMap'
  dsimp only [Batteries.RBMap.contains, Batteries.RBMap.find?, Option.map] at *
  split at H <;> cases H; simp [*]

seal merge_sem List.remove List.get in
theorem correct_threeway {T: Type _} [DecidableEq T]:
    @refines _ _ (@matching_three T) (fun (x : List T × List T) y => (x.1 ++ x.2).Perm y) := by
      intro ⟨ x1, x2 ⟩ y HPerm indis
      apply @comp_refines.mk _ _ (@matching_three T)
      . intro ident ⟨x'1, x'2⟩ v Hcontains Himod
        have := keysInMap'' _ _ Hcontains
        fin_cases this
        · dsimp at *
          
        · sorry
        · sorry
        have : ident = "a" := by sorry
        subst ident
        clear indisL indisR Hcontains this
        
        simp (config := {implicitDefEqProofs := false}) only [other, other', input_keys] at v Himod
        let (And.intro l r) := Himod; subst_vars; clear Himod
        constructor; constructor; and_intros
        · rfl
        · apply existSR.done
        · simp [*]
        · constructor <;> dsimp only
          · intro ident' new_i v_1 Hcontains Hrule
            have := keysInMap' _ _ Hcontains
            fin_cases this 
            · set_option trace.Meta.whnf true in simp at Hrule
          · intro ident' ⟨ new_i_1, new_i_2 ⟩ v_1 Hcontains HVal
            have := keysInMap' _ _ Hcontains
            fin_cases this
            let ⟨ ⟨ i, HVall, temp ⟩, HValr ⟩ := HVal; clear HVal
            rreduce_not_all at *; subst_vars
            constructor; constructor
            and_intros; rfl
            rreduce_not_all
            generalize h : mid_i.2.get i = y'
            have Ht : ∃ i, mid_i.2.get i = y' := by exists i
            rw [← List.mem_iff_get] at Ht
            have Hiff := List.Perm.mem_iff (a := y') He
            have Ht' : y' ∈ y := by rw [← Hiff]; simp; tauto
            rw [List.mem_iff_get] at Ht'
            rcases Ht' with ⟨ i', Ht'r ⟩
            constructor; exists i' + 1
            simp; tauto

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
