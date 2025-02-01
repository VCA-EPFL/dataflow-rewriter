
import DataflowRewriter.ExprLowLemmas
import DataflowRewriter.Rewrites.LoopRewriteCorrect
import Mathlib
import Aesop

--import DataflowRewriter.Rewrites.MatchGoal

namespace DataflowRewriter.LoopRewrite

open Batteries (AssocList)

--open matchGoal

open Lean hiding AssocList
open Meta Elab

open StringModule

section Proof

variable {Data : Type}
variable (DataS : String)
variable (f : Data → Data × Bool)

variable [Inhabited Data]



def apply (n : Nat) (i : Data) : Data × Bool :=
match n with
| 0 => (i, true)
| n' + 1 => f (apply n' i).fst

@[aesop safe unfold]
def iterate (i: Data) (n : Nat) (i': Data) : Prop :=
  (∀ m, m < n -> (apply f m i).snd = true) ∧ apply f n i = (i', false) ∧ n > 0

#print rhsGhostType

inductive state_relation : rhsGhostType Data -> Prop where
| intros : ∀ (s :  rhsGhostType Data) x_merge x_module x_branchD x_branchB x_tagT x_tagM x_tagD x_splitD x_splitB x_split_branchT x_split_branchF x_moduleT x_moduleF,
  ⟨ x_module, ⟨x_branchD, x_branchB⟩, x_merge, ⟨x_tagT, x_tagM, x_tagD ⟩, ⟨x_splitD, x_splitB⟩⟩ = s ->
  ( ∀ elem, elem ∈ x_tagD ->  elem.1 = elem.2.2 ∧ elem.2.1 = 0) ->
  (∀ elem n i', elem ∈ x_merge -> iterate f elem.2.2 n i' -> elem.2.1 ≥ 0 ∧ elem.2.1 < n ∧ elem.1.2 = (apply f elem.2.1 elem.2.2).1) ->
  List.map Prod.fst (List.filter (fun x => x.2 == true) (List.zip (x_branchD ++ x_splitD ) ( x_branchB ++ x_splitB))) = x_split_branchT ->
  List.map Prod.fst (List.filter (fun x => x.2 == false) (List.zip (x_branchD ++ x_splitD ) (x_branchB ++ x_splitB ))) = x_split_branchF ->
  List.map Prod.fst (List.filter (fun x => x.2 == true) (x_module)) = x_moduleT ->
  List.map Prod.fst (List.filter (fun x => x.2 == false) (x_module)) = x_moduleF ->
  (∀ elem , elem ∈ x_split_branchT ++ x_moduleT -> ∃ n i', iterate f elem.2.2 n i' ∧
    elem.2.1 > 0 ∧ elem.2.1 < n ∧ elem.1.2 = (apply f elem.2.1 elem.2.2).1) ->
  (∀ elem, elem ∈ x_split_branchF ++ x_moduleF ->  iterate f elem.2.2 elem.2.1 elem.1.2) ->
  ((((x_merge ++ (x_module.map Prod.fst) ++ x_splitD ++ x_branchD).map Prod.fst).map Prod.fst).Nodup) ->
  (∀ elem, elem ∈ ((x_merge ++ (x_module.map Prod.fst) ++ x_splitD ++ x_branchD).map (fun ((x, _), _, y) => (x, y)))-> elem ∈ x_tagT) ->
  ((x_tagT.map Prod.fst).Nodup) ->
  (x_branchD ++ x_splitD).length = (x_branchB ++ x_splitB).length ->
  ( ∀ tag d n i, x_tagM.find? tag = some (d, n, i) -> (tag, i ) ∈ x_tagT ∧ iterate f i n d) ->
  ( ∀ d, d ∈ x_tagD -> d.2 = (0, d.1)) ->
  state_relation s

inductive φ: rhsGhostType Data -> lhsType Data -> Prop where
| intro : ∀ (i:rhsGhostType Data) i_merge i_module i_branchD i_branchB i_tagT i_tagM i_tagD i_splitD i_splitB i_moduleT x_moduleF
            (s : lhsType Data) s_bag s_initL s_initB s_module s_splitD s_splitB s_branchD s_branchB s_forkR s_forkL s_muxB s_muxI s_muxC  s_branchD,
    ⟨i_module, ⟨i_branchD, i_branchB⟩, i_merge, ⟨i_tagT, i_tagM, i_tagD ⟩, ⟨i_splitD, i_splitB⟩⟩ = i ->
    ⟨s_bag, ⟨s_initL, s_initB⟩, s_module, ⟨s_splitD, s_splitB⟩ ,⟨s_branchD, s_branchB⟩, ⟨s_forkR, s_forkL⟩, s_muxB, s_muxI, s_muxC ⟩ = s ->

    φ i s




set_option maxHeartbeats 10000000

theorem alpa {α : Type} {a : α} {l : List α} : a :: l = [a] ++ l := by simp only [List.singleton_append]

attribute [aesop unsafe 50% forward] List.Nodup.cons List.perm_append_singleton
attribute [aesop norm] List.perm_comm

theorem apply_plus_one (i: Data) (n : Nat) : (f (apply f n i).1).1 = (apply f (n +1) i).1 := by admit

theorem apply_plus_one_condiction (i: Data) (n : Nat) : (f (apply f n i).1).2 = (apply f (n +1) i).2 := by admit

theorem apply_true (i i' : Data) (n : Nat) ( k : Nat) : k < n -> (apply f (k + 1) i).2 = true -> iterate f i n i' -> k + 1 < n := by admit

theorem apply_false (i i' : Data) (n : Nat) ( k : Nat) : k < n -> (apply f (k + 1) i).2 = false -> iterate f i n i' -> k + 1 = n := by admit


theorem erase_map {α β γ : Type} {a : α} {b : β} {c : γ} {l : List ((α × β) × γ)} {k : Nat} : List.map (Prod.fst ∘ Prod.fst) (List.eraseIdx l k) = (List.map (Prod.fst ∘ Prod.fst) l).eraseIdx k := by admit

theorem perm_comm {α : Type} {l1 l2 l3 : List α} : (l1).Perm (l2 ++ l3) -> (l1).Perm (l3 ++ l2) := by admit

theorem erase_perm  {α β γ : Type} {a : α} {b : β} {c : γ} {l : List ((α × β) × γ)} (k : Fin (List.length l)): ((List.map (Prod.fst ∘ Prod.fst) l).eraseIdx k ++ [(l[k].1.1)]).Perm (List.map (Prod.fst ∘ Prod.fst) l) := by admit

theorem map_fst {α β γ η  : Type} {i : α} {l : List ((α × β) × γ × η)}:  i ∈ (l.map Prod.fst).map Prod.fst -> ∃ i', (i, i') ∈ l.map (fun x => (x.1.1, x.2.2)) := by aesop

--theorem extract_condition {i i': Data} {k : Nat} {a : Bool} : apply f k i = (i', a) ->  (apply f k i).2 = a := by admit


theorem state_relation_preserve:
  ∀ (s s' : rhsGhostType Data) rule,
    rule ∈ ( rhsGhostEvaled f).internals ->
    rule s s' ->
    state_relation f s ->
    state_relation f s' := by
  intro s s' rule h1 h2 h3
  let ⟨ x_module, ⟨x_branchD, x_branchB⟩, x_merge, ⟨x_tagT, x_tagM, x_tagD ⟩, ⟨x_splitD, x_splitB⟩⟩ := s
  let ⟨ x_module', ⟨x_branchD', x_branchB'⟩, x_merge', ⟨x_tagT', x_tagM', x_tagD' ⟩, ⟨x_splitD', x_splitB'⟩⟩ := s'
  fin_cases h1
  -- . dsimp at h2
  --   obtain ⟨cons, newC, h⟩ := h2
  --   obtain ⟨ x_module', ⟨x_branchD', x_branchB'⟩, x_merge', ⟨x_tagT', x_tagM', x_tagD' ⟩, ⟨x_splitD', x_splitB'⟩⟩ := cons
  --   dsimp at h
  --   simp_all; repeat cases ‹_ ∧ _›
  --   subst_vars
  --   cases h3
  --   rename_i h h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 H13 H14 H15
  --   simp at h
  --   repeat cases ‹_ ∧ _›
  --   subst_vars
  --   constructor <;> (try rfl) <;> (try assumption)
  --   . clear h9 h10 h12
  --     intro elem h1
  --     specializeAll elem
  --     constructor
  --     . rw[← List.singleton_append] at *
  --       aesop (add norm List.mem_append_right) (config := {useDefaultSimpSet := false})
  --     . rw[← List.singleton_append] at *
  --       aesop (add norm List.mem_append_right) (config := {useDefaultSimpSet := false})
  --   . clear h9 h10 h12 H13 H14 H15
  --     intro elem n i' h1 h2
  --     specializeAll elem
  --     specializeAll n
  --     specializeAll i'
  --     simp_all
  --     cases h1
  --     . subst_vars
  --       aesop
  --     . aesop
  --   . clear h10 h9 h4 h3 H13 H14
  --     rename_i h _
  --     have h' := h
  --     specialize h newC.2.2
  --     --specialize h12 (newC.1.1, newC.2.2)
  --     rw[← List.singleton_append ]
  --     (repeat rw[List.map_append])
  --     have H : List.map Prod.fst (List.map Prod.fst [newC]) = [newC.1.1] := by simp
  --     rw[H]
  --     (repeat rw[← List.append_assoc])
  --     rw[List.append_assoc]; rw[List.append_assoc]; rw[List.append_assoc]
  --     rw[List.singleton_append ]
  --     rw[@List.nodup_cons _ newC.1.1 ]
  --     constructor
  --     . rename_i x_merge x_module x_branch _ _ _ x_split _ _
  --       by_cases newC.1.1 ∉ List.map Prod.fst (List.map Prod.fst x_merge) ++
  --           (List.map Prod.fst (List.map Prod.fst (List.map Prod.fst x_module)) ++
  --           (List.map Prod.fst (List.map Prod.fst x_split) ++ List.map Prod.fst (List.map Prod.fst x_branch)))
  --       . assumption
  --       . rename_i h; simp only [exists_and_right, exists_eq_right, Bool.exists_bool, not_or, not_exists, not_and, not_forall, not_not] at h
  --         simp only [ List.mem_append] at h12
  --         (repeat rw[← List.map_append] at h)
  --         have h := map_fst h
  --         cases h; rename_i i' h
  --         ac_nf at *
  --         specialize h12 (newC.1.1, i') h
  --         specialize h' i'
  --         solve_by_elim
  --     . (repeat rw[List.map_append] at h11)
  --       ac_nf at *
  --   . rename_i h14 h15
  --     clear h10 h9 h4 h11 h14 h15
  --     intro elem h1
  --     specialize h12 elem
  --     by_cases elem = (newC.1.1, newC.2.2)
  --     . obtain ⟨⟨ newCT, newCD⟩, newCN, newCDI⟩ := newC
  --       simp at h1
  --       simp_all
  --     . obtain ⟨⟨ newCT, newCD⟩, newCN, newCDI⟩ := newC
  --       subst_vars
  --       simp at h1
  --       simp_all
  --   . clear h10 h9 h4  H13 H14 H15
  --     rename_i hn _
  --     rename_i x_tag _ _ _ _
  --     rw[List.map_append]
  --     rw[List.nodup_append]
  --     constructor
  --     . assumption
  --     . constructor
  --       . simp
  --       . simp
  --         assumption
  --   . clear h10 h9 h4  H13 H15
  --     intro tag d n i h1
  --     specialize H14 tag d n i h1
  --     cases H14; rename_i H14 H14'
  --     constructor
  --     . simp_all
  --     . assumption
  --   . clear h10 h9 h4  H13 H14 h3 h11 h12
  --     intro d h1
  --     specialize H15 d
  --     simp at H15
  --     aesop
  -- . dsimp at h2
  --   obtain ⟨cons, newC, h⟩ := h2
  --   obtain ⟨ x_module', ⟨x_branchD', x_branchB'⟩, x_merge', ⟨x_tagT', x_tagM', x_tagD' ⟩, ⟨x_splitD', x_splitB'⟩⟩ := cons
  --   dsimp at h
  --   simp_all; repeat cases ‹_ ∧ _›
  --   subst_vars
  --   cases h3
  --   rename_i h h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 H13 H14 H15
  --   simp at h
  --   repeat cases ‹_ ∧ _›
  --   subst_vars
  --   constructor <;> (try rfl) <;> (try assumption)
  --   . clear h11 h12 h13 h9 h10
  --     rename_i h
  --     cases h; rename_i l h4
  --     cases h4
  --     subst_vars
  --     intro elem n i' h1
  --     specialize h4 elem n i'
  --     aesop (add safe forward List.mem_of_mem_eraseIdx)
  --   . clear h10 h12 h13 h11 H13
  --     intro elem
  --     specialize h9 elem
  --     unfold liftF2
  --     unfold liftF
  --     simp
  --     intro h1
  --     cases h1 <;> rename_i h
  --     . simp_all
  --     . cases h <;> rename_i h
  --       . simp_all
  --       . cases h
  --         --obtain ⟨ ⟨newCT, newCI ⟩, newCN, newCD ⟩ := newC
  --         specialize h4 newC
  --         rename_i H _ _
  --         cases H; rename_i l H
  --         cases H; rename_i H1 H2
  --         clear H1
  --         rename_i x_merge _ _ _ _ _ _ _ _ _ _
  --         have HH := List.get_mem x_merge l
  --         rw[List.get_eq_getElem] at HH; rw[← H2] at HH
  --         specialize h4 HH
  --         subst_vars; simp_all
  --         constructor
  --         . cases h4; rename_i H4 _
  --           rename_i H _
  --           rw[apply_plus_one_condiction] at H
  --           have HH := apply_true f x_merge[↑l].2.2 i' n x_merge[↑l].2.1 H4 H h2
  --           simp_all
  --         . apply apply_plus_one
  --   . clear h9 h12 h13 h11 H13
  --     intro elem n i'
  --     specialize h10 elem n i'
  --     unfold liftF2
  --     unfold liftF
  --     simp
  --     intro h1 h2
  --     cases h1 <;> rename_i h
  --     . simp_all
  --     . cases h <;> rename_i h
  --       . simp_all
  --       . cases h
  --         specialize h4 newC n i'
  --         rename_i H _ _
  --         cases H; rename_i l H
  --         cases H; rename_i H1 H2
  --         clear H1
  --         rename_i x_merge _ _ _ _ _ _ _ _ _ _
  --         have HH := List.get_mem x_merge l
  --         rw[List.get_eq_getElem] at HH; rw[← H2] at HH
  --         specialize h4 HH
  --         subst_vars; simp_all
  --         constructor
  --         . cases h4; rename_i H4 _
  --           rename_i H _
  --           rw[apply_plus_one_condiction] at H
  --           have HH := apply_false f x_merge[↑l].2.2 i' n x_merge[↑l].2.1 H4 H h2
  --           simp_all
  --         . cases h4; rename_i H4 _
  --           rename_i H _
  --           rw[apply_plus_one_condiction] at H
  --           have HH := apply_false f x_merge[↑l].2.2 i' n x_merge[↑l].2.1 H4 H h2
  --           subst HH
  --           apply apply_plus_one
  --   . clear h9 h12 h13 h10 h4
  --     unfold liftF2
  --     unfold liftF
  --     simp_all
  --     rename_i H
  --     cases H; rename_i l H
  --     cases H; rename_i H1 H2
  --     subst x_merge'
  --     simp_all
  --     ac_nf at *
  --     rename_i x_merge x_module x_branchD _ _ _ _ x_splitD _
  --     have H : (List.map (Prod.fst ∘ Prod.fst) (List.eraseIdx x_merge ↑l) ++
  --   (List.map (Prod.fst ∘ Prod.fst ∘ Prod.fst) x_module ++
  --     x_merge[↑l].1.1 :: (List.map (Prod.fst ∘ Prod.fst) x_splitD ++ List.map (Prod.fst ∘ Prod.fst) x_branchD))).Perm (List.map (Prod.fst ∘ Prod.fst) x_merge ++
  --   (List.map (Prod.fst ∘ Prod.fst ∘ Prod.fst) x_module ++
  --     (List.map (Prod.fst ∘ Prod.fst) x_splitD ++ List.map (Prod.fst ∘ Prod.fst) x_branchD))) := by
  --       (repeat rw[ ← List.append_assoc])
  --       rw[List.append_cons]
  --       rw[List.append_assoc _ (List.map (Prod.fst ∘ Prod.fst) x_splitD) (List.map (Prod.fst ∘ Prod.fst) x_branchD)]
  --       rw [List.perm_append_right_iff]
  --       simp
  --       rw [erase_map]
  --       . have hh := List.perm_append_comm_assoc ((List.map (Prod.fst ∘ Prod.fst) x_merge).eraseIdx ↑l) (List.map (Prod.fst ∘ Prod.fst ∘ Prod.fst) x_module) ([x_merge[↑l].1.1])
  --         have h1 := @List.Perm.trans _ _ _ (List.map (Prod.fst ∘ Prod.fst) x_merge ++ List.map (Prod.fst ∘ Prod.fst ∘ Prod.fst) x_module) hh
  --         apply h1
  --         clear hh h1
  --         apply perm_comm
  --         rw [List.perm_append_left_iff]
  --         apply erase_perm l
  --         . exact newC.1.1
  --         . exact newC.1.2
  --         . exact newC.2
  --       . exact newC.1.1
  --       . exact newC.1.2
  --       . exact newC.2
  --     have H := List.Perm.symm H
  --     apply List.Nodup.perm h11 H
  --   . clear h9 h10 h4 h11
  --     unfold liftF2
  --     unfold liftF
  --     simp only
  --     rename_i H
  --     cases H; rename_i l H
  --     cases H; rename_i H1 H2
  --     subst x_merge'
  --     intro elem h1
  --     simp_all
  --     specialize h12 elem
  --     apply h12
  --     clear h12
  --     cases h1
  --     . constructor
  --       aesop ( add safe forward List.mem_of_mem_eraseIdx) (config := {useDefaultSimpSet := false})
  --     . rename_i h
  --       cases h
  --       . aesop (config := {useDefaultSimpSet := false})
  --       . rename_i h; cases h
  --         . constructor
  --           constructor; rotate_left
  --           . exact newC.1.2
  --           . constructor; rotate_left
  --             . exact newC.2.1
  --             . constructor; rotate_left
  --               . exact newC.2.2
  --               . aesop
  --         . aesop (config := {useDefaultSimpSet := false})
  -- . dsimp at h2
  --   obtain ⟨cons, newC, h⟩ := h2
  --   obtain ⟨ x_module', ⟨x_branchD', x_branchB'⟩, x_merge', ⟨x_tagT', x_tagM', x_tagD' ⟩, ⟨x_splitD', x_splitB'⟩⟩ := cons
  --   dsimp at h
  --   simp_all; repeat cases ‹_ ∧ _›
  --   subst_vars
  --   cases h3
  --   rename_i h h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 H13 H14 H15
  --   simp at h
  --   repeat cases ‹_ ∧ _›
  --   subst_vars
  --   constructor <;> (try rfl) <;> (try assumption)
  --   . clear h10 h12 h13 h11
  --     intro elem n i'
  --     specialize h9 elem n i'
  --     intro h1 h2
  --     have h1' := @List.zip_append _ _ _ [newC.1] _ [newC.2] H13
  --     ac_nf at *
  --     have H : [newC] = [newC.1].zip [newC.2] := by simp
  --     --aesop (add safe forward [List.filter_append,List.map_append, List.singleton_append]) (config := {useDefaultSimpSet := false})
  --     rw[h1'] at h1
  --     rw[List.filter_append] at h1
  --     rw[List.map_append] at h1
  --     rw[← List.singleton_append ] at h9
  --     rw[List.filter_append] at h9
  --     rw[List.map_append] at h9
  --     rw[H] at h9
  --     ac_nf at *
  --     specialize h9 h1 h2
  --     assumption
  --   . clear h9 h12 h13 h11
  --     intro elem n i'
  --     specialize h10 elem n i'
  --     intro h1 h2
  --     have h1' := @List.zip_append _ _ _ [newC.1] _ [newC.2] H13
  --     ac_nf at *
  --     have H : [newC] = [newC.1].zip [newC.2] := by simp
  --     --aesop (add safe forward [List.filter_append,List.map_append, List.singleton_append]) (config := {useDefaultSimpSet := false})
  --     rw[h1'] at h1
  --     rw[List.filter_append] at h1
  --     rw[List.map_append] at h1
  --     rw[← List.singleton_append ] at h10
  --     rw[List.filter_append] at h10
  --     rw[List.map_append] at h10
  --     rw[H] at h10
  --     ac_nf at *
  --     specialize h10 h1 h2
  --     assumption
  --   . clear h9 h12 h13 h10 h4
  --     rw [← List.append_assoc ]
  --     rw[← List.singleton_append ] at h11
  --     (repeat rw[List.map_append])
  --     (repeat rw[List.map_append] at h11)
  --     have H : List.map Prod.fst [newC] = [newC.1] := by simp
  --     rw[H] at h11
  --     simp_all
  --     (repeat rw[← List.append_assoc])
  --     rw[List.nodup_middle] at h11
  --     rename_i x_branch _ _ _ _ _ x_split _
  --     rw[List.nodup_middle]
  --     ac_nf at *
  --   . clear h9 h10 h4 h11 h13 h3 H13
  --     intro elem h1
  --     specialize h12 elem
  --     aesop
  --     -- rw[← List.singleton_append ] at h12
  --     -- (repeat rw[List.map_append] at h12)
  --     -- (repeat rw[List.map_append] at h1)
  --     -- aesop
  --     -- have H : (List.map Prod.fst [newC]) = [newC.1] := by simp
  --     -- rw[H] at h12
  --     -- (repeat rw[List.mem_append] at h12)
  --     -- (repeat rw[List.mem_append] at h1)
  --     -- aesop
  --   . clear h3 h4 h13 h11 h12 h9 h10
  --     (repeat rw [← List.append_assoc ])
  --     (repeat rw [List.length_append])
  --     (repeat rw [List.length_append] at H13)
  --     rw[H13]
  --     simp
  -- . dsimp at h2
  --   obtain ⟨cons, newC, h⟩ := h2
  --   obtain ⟨ x_module', ⟨x_branchD', x_branchB'⟩, x_merge', ⟨x_tagT', x_tagM', x_tagD' ⟩, ⟨x_splitD', x_splitB'⟩⟩ := cons
  --   dsimp at h
  --   simp_all; repeat cases ‹_ ∧ _›
  --   subst_vars
  --   cases h3
  --   rename_i h h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 H13 H14 H15
  --   simp at h
  --   repeat cases ‹_ ∧ _›
  --   subst_vars
  --   constructor <;> (try rfl) <;> (try assumption)
  --   . clear h10 h12 h13 h11 h4 h3
  --     intro elem n i'
  --     specialize h9 elem n i'
  --     intro h1 h2
  --     rw[← List.singleton_append ] at h9
  --     ac_nf at *
  --     specialize h9 h1 h2
  --     assumption
  --   . clear h9 h12 h13 h11
  --     intro elem n i'
  --     specialize h10 elem n i'
  --     intro h1 h2
  --     rw[← List.singleton_append ] at h10
  --     ac_nf at *
  --     specialize h10 h1 h2
  --     assumption
  --   . clear h9 h12 h13 h10 h4
  --     rw [List.append_assoc ] at h11
  --     rw[← List.singleton_append ] at h11
  --     (repeat rw[List.map_append])
  --     (repeat rw[List.map_append] at h11)
  --     --have H : List.map Prod.fst [newC] = [newC.1] := by simp
  --     --rw[H] at h11
  --     simp_all
  --     (repeat rw[← List.append_assoc])
  --     (repeat rw[← List.append_assoc] at h11)
  --     rename_i x_merge x_module _ _ _ _ _ _
  --     rw[@List.nodup_middle _  _ (List.map (Prod.fst ∘ Prod.fst) x_merge ++ List.map (Prod.fst ∘ Prod.fst ∘ Prod.fst) x_module)] at h11
  --     rw[List.nodup_middle]
  --     ac_nf at *
  --   . clear h9 h10 h4 h11 h13 h3 H13
  --     intro elem h1
  --     specialize h12 elem
  --     aesop
  --   . clear h3 h4 h13 h11 h12 h9 h10
  --     (repeat rw [← List.append_assoc ])
  --     (repeat rw [List.length_append])
  --     rw[← List.singleton_append ] at H13
  --     (repeat rw [List.length_append] at H13)
  --     rw[← H13]
  --     ac_nf at *
  -- . dsimp at h2
  --   obtain ⟨cons, newC, h⟩ := h2
  --   . obtain ⟨ x_module', ⟨x_branchD', x_branchB'⟩, x_merge', ⟨x_tagT', x_tagM', x_tagD' ⟩, ⟨x_splitD', x_splitB'⟩⟩ := cons
  --     dsimp at h
  --     simp_all; repeat cases ‹_ ∧ _›
  --     subst_vars
  --     cases h3
  --     rename_i h h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 H13 H14 H15
  --     simp at h
  --     repeat cases ‹_ ∧ _›
  --     subst_vars
  --     constructor <;> (try rfl) <;> (try assumption)
  --     . clear h10 h12 h13 h11 h4 h3
  --       intro elem n i'
  --       specialize h9 elem n i'
  --       intro h1 h2
  --       rw[← List.singleton_append ] at h9
  --       ac_nf at *
  --       specialize h9 h1 h2
  --       assumption
  --     . clear h9 h12 h13 h11
  --       intro elem n i'
  --       specialize h10 elem n i'
  --       intro h1 h2
  --       rw[← List.singleton_append ] at h10
  --       ac_nf at *
  --       specialize h10 h1 h2
  --       assumption
  --     . clear h3 h4 h13 h11 h12 h9 h10
  --       (repeat rw [← List.append_assoc ])
  --       (repeat rw [List.length_append])
  --       rw[← List.singleton_append ] at H13
  --       (repeat rw [List.length_append] at H13)
  --       rw[H13]
  --       ac_nf at *
  --   . obtain ⟨ x_module', ⟨x_branchD', x_branchB'⟩, x_merge', ⟨x_tagT', x_tagM', x_tagD' ⟩, ⟨x_splitD', x_splitB'⟩⟩ := cons
  --     rename_i h
  --     dsimp at h
  --     simp_all; repeat cases ‹_ ∧ _›
  --     subst_vars
  --     cases h3
  --     rename_i h h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 H13 H14 H15
  --     simp at h
  --     repeat cases ‹_ ∧ _›
  --     subst_vars
  --     constructor <;> (try rfl) <;> (try assumption)
  --     . clear h10 h12 h13 h11 h4 h3
  --       intro elem n i'
  --       specialize h9 elem n i'
  --       intro h1 h2
  --       rw[← List.singleton_append ] at h9
  --       ac_nf at *
  --       specialize h9 h1 h2
  --       assumption
  --     . clear h9 h12 h13 h11
  --       intro elem n i'
  --       specialize h10 elem n i'
  --       intro h1 h2
  --       rw[← List.singleton_append ] at h10
  --       ac_nf at *
  --       specialize h10 h1 h2
  --       assumption
  --     . clear h3 h4 h13 h11 h12 h9 h10
  --       (repeat rw [← List.append_assoc ])
  --       (repeat rw [List.length_append])
  --       rw[← List.singleton_append ] at H13
  --       (repeat rw [List.length_append] at H13)
  --       rw[H13]
  --       ac_nf at *
  -- . dsimp at h2
  --   obtain ⟨cons, newC, h⟩ := h2
  --   obtain ⟨ x_module', ⟨x_branchD', x_branchB'⟩, x_merge', ⟨x_tagT', x_tagM', x_tagD' ⟩, ⟨x_splitD', x_splitB'⟩⟩ := cons
  --   dsimp at h
  --   simp_all; repeat cases ‹_ ∧ _›
  --   subst_vars
  --   cases h3
  --   rename_i h h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 H13 H14 H15
  --   simp at h
  --   repeat cases ‹_ ∧ _›
  --   subst_vars
  --   constructor <;> (try rfl) <;> (try assumption)
  --   . clear h10 h12 H13 h13
  --     intro elem n i' h1 h2
  --     specialize h4 elem n i'
  --     specialize h9 elem n i'
  --     cases h1
  --     . simp_all
  --     . rename_i h
  --       specialize h4 h h2
  --       assumption
  --   . clear h10 h12 h13 h11 h4 h3
  --     intro elem n i'
  --     specialize h9 elem n i'
  --     intro h1 h2
  --     rw[← List.singleton_append ] at h9
  --     rw[← @List.singleton_append _ true ] at h9
  --     ac_nf at h9
  --     rw[List.zip_append] at h9
  --     (repeat rw[List.filter_append] at h9)
  --     (repeat rw[List.filter_append] at h1)
  --     (repeat rw[List.map_append] at h9)
  --     (repeat rw[List.map_append] at h1)
  --     have h1 := List.mem_append_right (List.map Prod.fst (List.filter (fun x => x.2 == true) ([newC].zip [true]))) h1
  --     ac_nf at *
  --     specialize h9 h1 h2
  --     . assumption
  --     . simp
  --   . clear h9 h12 h13 h10 h4 H13
  --     rw [List.append_assoc ] at h11
  --     rw[← List.singleton_append ] at h11
  --     rw[← List.singleton_append ]
  --     (repeat rw[List.map_append])
  --     (repeat rw[List.map_append] at h11)
  --     (repeat rw[← List.append_assoc ] at h11)
  --     rename_i x_merge x_module _ _ _ x_splitD _
  --     have H := @List.nodup_append _ (List.map Prod.fst (List.map Prod.fst x_merge) ++ List.map Prod.fst (List.map Prod.fst (List.map Prod.fst x_module)) ++ (List.map Prod.fst (List.map Prod.fst x_splitD)))
  --                  (List.map Prod.fst (List.map Prod.fst [newC]) ++ List.map Prod.fst (List.map Prod.fst x_branchD'))
  --     cases H; rename_i H1 H2; clear H2
  --     ac_nf at *
  --     rw [List.nodup_append_comm]
  --     specialize H1 h11
  --     let ⟨ H1, H3, H4 ⟩ := H1
  --     rw [List.nodup_append_comm ] at H1
  --     have HH := List.Nodup.append H3 H1
  --     rename_i H
  --     clear h11 H1 H3 H
  --     rw[List.disjoint_append_right] at H4
  --     ac_nf at *
  --     cases H4; rename_i H41 H42
  --     have H := @List.disjoint_append_right _  (List.map Prod.fst (List.map Prod.fst x_merge) ++
  --     (List.map Prod.fst (List.map Prod.fst (List.map Prod.fst x_module)) ++
  --       List.map Prod.fst (List.map Prod.fst x_splitD))) (List.map Prod.fst (List.map Prod.fst x_branchD')) (List.map Prod.fst (List.map Prod.fst [newC]))
  --     cases H; rename_i H
  --     ac_nf at *
  --     have H4d := And.intro H41 H42
  --     specialize H H4d
  --     specialize HH H
  --     assumption
  --   . clear h9 h10 h4 h11 h13 h3 H13
  --     intro elem h1
  --     specialize h12 elem
  --     aesop
  --   . clear h3 h4 h13 h11 h12 h9 h10
  --     (repeat rw [← List.append_assoc ])
  --     (repeat rw [List.length_append])
  --     rw[← List.singleton_append ] at H13
  --     rw[← @List.singleton_append _ true] at H13
  --     (repeat rw [List.length_append] at H13)
  --     (repeat rw[List.length_singleton] at H13)
  --     omega
  -- . dsimp at h2
  --   obtain ⟨cons, newC, h⟩ := h2
  --   obtain ⟨ x_module', ⟨x_branchD', x_branchB'⟩, x_merge', ⟨x_tagT', x_tagM', x_tagD' ⟩, ⟨x_splitD', x_splitB'⟩⟩ := cons
  --   dsimp at h
  --   simp_all; repeat cases ‹_ ∧ _›
  --   subst_vars
  --   cases h3
  --   rename_i h h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 H13 H14 H15
  --   simp at h
  --   repeat cases ‹_ ∧ _›
  --   subst_vars
  --   constructor <;> (try rfl) <;> (try assumption)
  --   . clear h9 h12 H13 h13
  --     intro elem
  --     specialize h10 elem
  --     intro h1
  --     rw[← List.singleton_append ] at h10
  --     rw[← @List.singleton_append _ false ] at h10
  --     ac_nf at h10
  --     rw[List.zip_append] at h10
  --     (repeat rw[List.filter_append] at h9)
  --     (repeat rw[List.filter_append] at h1)
  --     (repeat rw[List.map_append] at h9)
  --     (repeat rw[List.map_append] at h1)
  --     have h1 := List.mem_append_right (List.map Prod.fst (List.filter (fun x => x.2 == true) ([newC].zip [true]))) h1
  --     ac_nf at *
  --     specialize h10 h1
  --     . assumption
  --     . simp
  --   . clear h9 h12 h13 h10 h4 H13
  --     rename_i x_merge x_module _ _ _ x_splitD _ _ _
  --     rw [List.append_assoc ] at h11
  --     rw[← List.singleton_append ] at h11
  --     (repeat rw[List.map_append])
  --     (repeat rw[List.map_append] at h11)
  --     have H : List.map Prod.fst (List.map Prod.fst [newC]) = [newC.1.1] := by simp
  --     rw[H] at h11
  --     rw[List.singleton_append ] at h11
  --     (repeat rw[← List.append_assoc ] at h11)
  --     rw[List.nodup_middle] at h11
  --     rw[List.nodup_cons ] at h11
  --     cases h11; assumption
  --   . clear h9 h10 h4 h11 h13 h3 H13
  --     intro elem h1
  --     specialize h12 elem
  --     aesop
  --   . clear h3 h4 h13 h11 h12 h9 h10
  --     (repeat rw [← List.append_assoc ])
  --     (repeat rw [List.length_append])
  --     rw[← List.singleton_append ] at H13
  --     rw[← @List.singleton_append _ false] at H13
  --     (repeat rw [List.length_append] at H13)
  --     (repeat rw[List.length_singleton] at H13)
  --     omega
  --   . clear h4 h11 h9
  --     intro tag d n i h1
  --     by_cases tag = newC.1.1
  --     . subst_vars
  --       simp at h1
  --       cases h1; subst_vars
  --       rename_i h; let ⟨⟨ newc11, newc12⟩ , newc21, newc22⟩ := newC
  --       cases h
  --       dsimp at *
  --       specialize h12 (newc11, i)
  --       simp at h12
  --       constructor
  --       . assumption
  --       . specialize h10 ((newc11, newc12), n, i)
  --         simp at h10
  --         assumption
  --     . apply H14
  --       rw[Batteries.AssocList.find?.eq_2] at h1
  --       aesop







end Proof
end DataflowRewriter.LoopRewrite
