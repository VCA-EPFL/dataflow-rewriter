import Leanses
import Lean
import Init.Data.BitVec.Lemmas
import Mathlib
import Qq

import DataflowRewriter.Simp
import DataflowRewriter.Module
import DataflowRewriter.Component
import DataflowRewriter.List

open Qq

open Batteries (AssocList)
open Batteries (RBMap)

open Lean.Meta Lean.Elab

namespace DataflowRewriter

def build_module (e : ExprLow) (map : IdentMap ((T : Type _) × Module T)) (proof : (build_module' e map).isSome = true := by decide):  (T : Type _) × Module T := 
  (build_module' e map).get proof

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

@[simp]
def merge_sem (T: Type _) :=
  match build_module' mergeLow (RBMap.ofList [("merge", ⟨List T, merge T⟩)] _) with
  | some x => x
  | none => ⟨Unit, empty⟩

attribute [dmod] AssocList.find? BEq.beq decide instIdentDecidableEq instDecidableEqString String.decEq RBMap.ofList RBMap.find? RBMap.findEntry? Batteries.RBSet.ofList Batteries.RBSet.insert Option.map Batteries.RBSet.findP? Batteries.RBNode.find? compare compareOfLessAndEq

#check RBMap.findD

-- theorem help : .isSome = true := by

set_option maxHeartbeats 0 in
example : ((merge_sem T).snd.inputs.getIO "a").fst = T := by
  simp (config := {implicitDefEqProofs := false}) [dmod]

instance : Repr (Option A) where
  reprPrec | (some a) => fun _ => "some"    
           | none => fun _ => "none"

theorem interface_match T :  matching_interface (merge_sem T).snd (threemerge T) := by
  constructor
  · intro ident
    have : ident = "a" := sorry
    subst ident
    trans T
    

theorem correct_threeway {T: Type _} [DecidableEq T]:
    refines ((merge_sem T).snd) (threemerge T) (interface_match T)
          (fun x y => (x.1 ++ x.2).Perm y) := by
      simp [threemerge, refines]
      intro x1 x2 y He indis
      rcases indis with ⟨indisL, indisR⟩
      constructor <;> dsimp at *
      . intro ident mid_i v Hi
        (fin_cases ident <;> dsimp at *)
        · constructor; constructor; and_intros
          · rfl
          · apply existSR.done
          · rcases Hi with ⟨ Hl, Hr ⟩
            rw [Hl]; subst x2
            simp [*]
          · constructor <;> dsimp only
            · intro ident' new_i v_1 Hrule
              fin_cases ident' <;> simp
            · intros ident' new_i v_1 HVal
              fin_cases ident'; simp
              reduce at *
              rcases Hi with ⟨ Hil, Hir ⟩
              rcases HVal with ⟨ ⟨ i, HVall, temp ⟩, HValr ⟩
              subst x2; subst v_1
              generalize h : mid_i.2.get i = y'
              have Ht : ∃ i, mid_i.2.get i = y' := by exists i
              rw [← List.mem_iff_get] at Ht
              have Hiff := List.Perm.mem_iff (a := y') He
              have Ht' : y' ∈ y := by rw [← Hiff]; simp; tauto
              rw [List.mem_iff_get] at Ht'
              rcases Ht' with ⟨ i', Ht'r ⟩
              constructor; exists i' + 1
              simp; tauto
        · constructor; constructor; and_intros
          · rfl
          · apply existSR.done
          · rcases Hi with ⟨ Hl, Hr ⟩
            rw [Hl]; subst x2
            simp [*]
          · constructor
            · intros ident' new_i v_1 Hrule
              fin_cases ident' <;> simp
            · intros ident' new_i v_1 HVal
              fin_cases ident'; simp
              reduce at *
              rcases Hi with ⟨ Hil, Hir ⟩
              rcases HVal with ⟨ ⟨ i, HVall, temp ⟩, HValr ⟩
              subst x2; subst v_1
              generalize h : mid_i.2.get i = y'
              have Ht : ∃ i, mid_i.2.get i = y' := by exists i
              rw [← List.mem_iff_get] at Ht
              have Hiff := List.Perm.mem_iff (a := y') He
              have Ht' : y' ∈ y := by rw [← Hiff]; simp; tauto
              rw [List.mem_iff_get] at Ht'
              rcases Ht' with ⟨ i', Ht'r ⟩
              constructor; exists i' + 1
              simp; tauto
        · constructor; constructor; and_intros
          · rfl
          · apply existSR.done
          · rcases Hi with ⟨ Hl, Hr ⟩
            rw [Hl]; subst x1
            rw [List.perm_comm]
            apply List.perm_cons_append_cons; rw [List.perm_comm]; assumption
          · constructor
            · intros ident' new_i v_1 Hrule
              fin_cases ident' <;> simp
            · intros ident' new_i v_1 HVal
              fin_cases ident'; simp
              reduce at *
              rcases Hi with ⟨ Hil, Hir ⟩
              rcases HVal with ⟨ ⟨ i, HVall, temp ⟩, HValr ⟩
              subst x1; subst v_1
              generalize h : mid_i.2.get i = y'
              have Ht : ∃ i', mid_i.2.get i' = y' := by exists i
              rw [← List.mem_iff_get] at Ht
              -- FAILS???: rw [Hil] at Ht
              have Ht' : y' ∈ v :: x2 := by rw [← Hil]; assumption
              rcases Ht' with _ | Ht'
              · constructor; exists 0
              · rename_i Ht';
                have Hiff := List.Perm.mem_iff (a := y') He
                have : y' ∈ y := by rw [← Hiff]; simp; tauto
                rw [List.mem_iff_get] at this
                rcases this with ⟨ i, Hl ⟩
                constructor; exists i + 1
                simp; tauto
      . intro ident mid_i v Hi
        fin_cases ident <;> dsimp only at * <;> reduce at *
        rcases Hi with ⟨ ⟨ i, Hil ⟩, Hir ⟩
        reduce at *
        rcases Hil with ⟨ Hill, Hilr ⟩
        subst v; subst x1
        generalize Hx2get : x2.get i = v'
        have Hx2in : v' ∈ x2 := by rw [List.mem_iff_get]; tauto
        have Hiff := List.Perm.mem_iff (a := v') He
        have Hyin : v' ∈ y := by rw [← Hiff]; simp; tauto
        rw [List.mem_iff_get] at Hyin
        rcases Hyin with ⟨ i', Hyget ⟩
        have HerasePerm : (mid_i.1.append mid_i.2).Perm (y.eraseIdx i'.1) := by
          simp [Hill]
          trans; apply List.perm_append_comm
          rw [←List.eraseIdx_append_of_lt_length] <;> [skip; apply i.isLt]
          trans ((x2 ++ mid_i.1).erase x2[i])
          have H2 : x2[i] = (x2 ++ mid_i.1)[i] := by
            symm; apply List.getElem_append_left
          rw [H2]; symm; apply List.erase_get
          symm; trans; symm; apply List.erase_get
          rw [Hyget]; simp at Hx2get; simp; rw [Hx2get]
          apply List.perm_erase; symm
          symm; trans; symm; assumption
          apply List.perm_append_comm
        constructor; constructor; and_intros
        · exists i'; and_intros; rfl; tauto
        · apply existSR.done
        · assumption
        · constructor <;> dsimp only
          · intro ident' new_i v_1 Hrule
            fin_cases ident' <;> simp
          · intros ident' new_i v_1 HVal
            fin_cases ident'
            reduce at *
            rcases HVal with ⟨ ⟨ i'', HVall, temp ⟩, HValr ⟩
            subst v'; subst v_1
            dsimp at *
            have : mid_i.2[i''] ∈ (x2.eraseIdx i.1) := by
              simp [Hill]; apply List.getElem_mem
            have : mid_i.2[i''] ∈ (mid_i.1 ++ x2.eraseIdx i.1) := by
              rw [List.mem_eraseIdx_iff_getElem] at this; simp; right
              simp at *; simp [Hill]; apply List.getElem_mem
            have HPermIn : mid_i.2[i''] ∈ y.eraseIdx i' := by
              rw [List.Perm.mem_iff]; assumption; symm
              rw [←Hill]; assumption
            rw [List.mem_iff_getElem] at HPermIn
            rcases HPermIn with ⟨ Ha, Hb, Hc ⟩
            constructor; exists ⟨ Ha, Hb ⟩; tauto
      · intro ident mid_i Hv
        fin_cases ident
        rcases Hv with ⟨ la, lb, vout, ⟨ ⟨ i, H2, H3 ⟩, Hx3 ⟩, ⟨ Hx2, H4 ⟩ ⟩; subst lb; subst la; subst vout
        constructor; and_intros
        · apply existSR.done
        · rw [Hx2,← H4,←List.eraseIdx_append_of_lt_length] <;> [skip; apply i.isLt]
          dsimp only;
          trans ((x1 ++ x1[i] :: x2).erase x1[i])
          rw [List.perm_comm]
          have : x1[↑i] = x1.get i := by simp
          simp [*] at *
          have H : x1[↑i] = (x1 ++ x1[↑i] :: x2)[↑i] := by
            symm; apply List.getElem_append_left
          dsimp at *; conv => arg 1; arg 2; rw [H]
          apply List.erase_get
          trans ((x1[i] :: (x1 ++ x2)).erase x1[i])
          apply List.perm_erase; simp
          rw [List.erase_cons_head]; assumption
        · constructor
          · intros ident' new_i v_1 Hrule
            fin_cases ident' <;> simp
          · intros ident' new_i v_1 HVal
            fin_cases ident'
            reduce at *
            rcases HVal with ⟨ ⟨ i', _, temp ⟩, _ ⟩
            subst v_1
            generalize h : mid_i.2.get i' = y'
            have Ht : ∃ i', mid_i.2.get i' = y' := by exists i'
            rw [← List.mem_iff_get] at Ht
            have Hiff := List.Perm.mem_iff (a := y') He
            have Ht'' : y' ∈ x1.get i :: x2 := by rw [←Hx2]; assumption
            simp at Ht''; rcases Ht'' with (Ht'' | Ht'')
            · have Ht' : y' ∈ y := by
                rw [List.Perm.mem_iff]; rotate_left; rewrite [List.perm_comm]; assumption; subst y'
                rw [Ht'']; simp; left; apply List.getElem_mem
              dsimp; apply List.getElem_of_mem at Ht'; rcases Ht' with ⟨ Ha, Hb, Hc ⟩
              constructor; exists ⟨ Ha, Hb ⟩; and_intros; rfl; symm; assumption
            · have Ht' : y' ∈ y := by
                rw [List.Perm.mem_iff]; rotate_left; rewrite [List.perm_comm]; assumption; subst y'
                simp; tauto
              dsimp; apply List.getElem_of_mem at Ht'; rcases Ht' with ⟨ Ha, Hb, Hc ⟩
              constructor; exists ⟨ Ha, Hb ⟩; and_intros; rfl; symm; assumption

end DataflowRewriter
