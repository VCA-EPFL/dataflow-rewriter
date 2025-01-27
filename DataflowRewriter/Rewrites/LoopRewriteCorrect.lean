/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.Rewrites.LoopRewrite
import DataflowRewriter.ExprLowLemmas
import DataflowRewriter.ExprHighElaborator

namespace DataflowRewriter.LoopRewrite

open Batteries (AssocList)

open Lean hiding AssocList
open Meta Elab

open StringModule

section Proof

variable {Data : Type}
variable (DataS : String)
variable (f : Data → Data × Bool)

variable [Inhabited Data]

attribute [drcompute] Batteries.AssocList.toList Function.uncurry Module.mapIdent List.toAssocList List.foldl
  Option.pure_def Option.bind_eq_bind Option.bind_some Module.renamePorts
  Batteries.AssocList.mapKey InternalPort.map toString Nat.repr Nat.toDigits Nat.toDigitsCore Nat.digitChar
  List.asString Batteries.AssocList.mapVal Batteries.AssocList.eraseAll Batteries.AssocList.eraseP
  beq_self_eq_true Option.getD cond beq_self_eq_true  beq_iff_eq  InternalPort.mk.injEq  String.reduceEq and_false
  imp_self BEq.beq Module.bijectivePortRenaming ExprLow.filterId List.Nodup List.inter AssocList.keysList List.filter
  List.elem AssocList.eraseAllP

attribute [drdecide] InternalPort.mk.injEq and_false decide_False decide_True and_true Batteries.AssocList.eraseAllP
  InternalPort.mk.injEq
  and_false  decide_False  decide_True  reduceCtorEq  cond  List.map List.empty_eq decide_true ne_eq List.pairwise_cons
  List.mem_singleton forall_eq
  InternalPort.mk.injEq String.reduceEq and_false not_false_eq_true List.not_mem_nil IsEmpty.forall_iff
  implies_true List.Pairwise.nil and_self Bool.and_self reduceCtorEq reduceIte decide_false and_true
  List.remove List.get_eq_getElem eq_mp_eq_cast cast_eq Prod.exists forall_const not_true_eq_false imp_self
  List.append_nil

def rewriteLhsRhs := rewrite.rewrite [DataS] |>.get rfl

def environmentLhs : IdentMap String (TModule1 String) := lhs Data DataS f |>.snd

def environmentRhs : IdentMap String (TModule1 String) := rhs Data DataS f |>.snd

/--
info: ["branch T", "pure f", "mux T", "init Bool false", "fork2 Bool", "split T Bool", "bag T"]
-/
#guard_msgs in
#eval @environmentLhs Unit "T" (λ _ => default) _ |>.keysList

-- /--
-- info: ["pure f", "merge T 2", "branch T", "split T Bool"]
-- -/
-- #guard_msgs in
-- #eval @environmentRhs Unit "T" (λ _ => default) _ |>.keysList

open Lean Meta Simp in
/-- Simplification procedure for decide expressions that tries to prove
    `decide x = true` or `decide x = false` using `rfl` -/
-- def decideSimproc : Simproc := fun e => do
--   match e with
--   | .app (.app (.const ``decide _) x) _ => do
--     -- Try to prove equality with true
--     return .done { expr := .const ``false [] }
--   | _ => return .continue

-- simproc decideSimproc_def (@decide _ _) := decideSimproc

-- #check String
-- theorem decide_simproc_theorem :
--   decide ("a" = "a") = false := by
--     simp only [decideSimproc_def]

@[drcompute] theorem find?_bag_data : (Batteries.AssocList.find? ("bag " ++ DataS) (environmentLhs DataS f)) = .some ⟨_, bag Data⟩ := by
  unfold environmentLhs lhs
  simp
  exists "bag " ++ DataS
  sorry

@[drcompute] theorem find?_init_data : (Batteries.AssocList.find? ("init Bool false") (environmentLhs DataS f)) = .some ⟨_, init Bool false⟩ := sorry
@[drcompute] theorem find?_branch_data : (Batteries.AssocList.find? ("branch " ++ DataS) (environmentLhs DataS f)) = .some ⟨_, branch Data⟩ := sorry
@[drcompute] theorem find?_pure_f : (Batteries.AssocList.find? ("pure f") (environmentLhs DataS f)) = .some ⟨_, pure f⟩ := sorry
@[drcompute] theorem find?_mux_data : (Batteries.AssocList.find? ("mux " ++ DataS) (environmentLhs DataS f)) = .some ⟨_, mux Data⟩ := sorry
@[drcompute] theorem find?_fork_bool : (Batteries.AssocList.find? ("fork2 Bool") (environmentLhs DataS f)) = .some ⟨_, fork2 Bool⟩ := sorry
@[drcompute] theorem find?_split_data : (Batteries.AssocList.find? ("split " ++ DataS ++ " Bool") (environmentLhs DataS f)) = .some ⟨_, split Data Bool⟩ := sorry

-- @[drcompute] theorem find?_fork_bool2 : (Batteries.AssocList.find? ("fork2 Bool") (environmentRhs DataS f)) = .some ⟨_, fork2 Bool⟩ := sorry
@[drcompute] theorem find?_branch_data2 : (Batteries.AssocList.find? ("branch (TagT × " ++ DataS ++ ")") (environmentRhs DataS f)) = .some ⟨_, branch (TagT × Data)⟩ := sorry
@[drcompute] theorem find?_pure_f2 : (Batteries.AssocList.find? ("pure (liftF f)") (environmentRhs DataS f)) = .some ⟨_, pure (liftF (γ := TagT) f)⟩ := sorry
@[drcompute] theorem find?_merge_data2 : (Batteries.AssocList.find? ("merge (TagT × " ++ DataS ++ ") 2") (environmentRhs DataS f)) = .some ⟨_, merge (TagT × Data) 2⟩ := sorry
@[drcompute] theorem find?_split_data2 : (Batteries.AssocList.find? ("split (TagT × " ++ DataS ++ ") Bool") (environmentRhs DataS f)) = .some ⟨_, split (TagT × Data) Bool⟩ := sorry
@[drcompute] theorem find?_tagger_data2 : (Batteries.AssocList.find? ("tagger_untagger_val TagT " ++ DataS ++ " " ++ DataS) (environmentRhs DataS f)) = .some ⟨_, tagger_untagger_val TagT Data Data⟩ := sorry

def lhsTypeEvaled : Type := by
  precomputeTac ([T| (rewriteLhsRhs DataS).input_expr, environmentLhs DataS f ]) by
    simp [drunfold,seval,drcompute,drdecide]
    -- rw [find?_bag_data,find?_init_data,find?_branch_data,find?_pure_f,find?_mux_data,find?_fork_bool,find?_split_data]
    -- simp

#eval [e|(DataflowRewriter.ExprLow.base
                      { input := Batteries.AssocList.cons
                                   { inst := DataflowRewriter.InstIdent.top, name := "in1" }
                                   { inst := DataflowRewriter.InstIdent.internal "bag", name := "in1" }
                                   (Batteries.AssocList.nil),
                        output := Batteries.AssocList.cons
                                    { inst := DataflowRewriter.InstIdent.top, name := "out1" }
                                    { inst := DataflowRewriter.InstIdent.top, name := "o_out" }
                                    (Batteries.AssocList.nil) }
                      "bag T"), environmentLhs "T" (λ _ => ((), true))].outputs.keysList

#eval ([e| (rewriteLhsRhs "T").input_expr, environmentLhs "T" (λ _ => ((), true)) ]).outputs.keysList

variable (Data) in
abbrev lhsType := (List Data ×
          NatModule.Named "init" (List Bool × Bool) ×
            NatModule.Named "pure" (List (Data × Bool)) ×
              NatModule.Named "split" (List Data × List Bool) ×
                NatModule.Named "branch" (List Data × List Bool) ×
                  NatModule.Named "fork2" (List Bool × List Bool) ×
                    NatModule.Named "mux" (List Data × List Data × List Bool))

set_option maxHeartbeats 0 in
def lhsEvaled : Module String (lhsType Data) := by
  precomputeTac [e| (rewriteLhsRhs DataS).input_expr, environmentLhs DataS f ] by
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq]
    rw [find?_bag_data,find?_init_data,find?_branch_data,find?_pure_f,find?_mux_data,find?_fork_bool,find?_split_data]
    simp [-AssocList.find?_eq]
    unfold Module.liftR Module.liftL
    dsimp
    -- repeat
    --   conv in (Module.bijectivePortRenaming _ _) =>
    --     congr <;> simp +ground +autoUnfold [drunfold,-AssocList.find?_eq]
    --   conv in (Module.bijectivePortRenaming _ _) => simp [Module.bijectivePortRenaming, drunfold,-AssocList.find?_eq]
    conv =>
      pattern (occs := *) Module.connect'' _ _
      all_goals
        rw [(Module.connect''_dep_rw (h := by simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?]; rfl)
                                     (h' := by simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?]; rfl))]; rfl
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,-Prod.exists]
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?,AssocList.filter,-Prod.exists]
    unfold Module.connect''
    dsimp

variable (Data) in
abbrev rhsType :=
        (NatModule.Named "pure" (List ((TagT × Data) × Bool)) ×
          NatModule.Named "branch" (List (TagT × Data) × List Bool) ×
            NatModule.Named "merge" (List (TagT × Data)) ×
              NatModule.Named "tagger_untagger_val" (List TagT × AssocList TagT Data × List Data) ×
                NatModule.Named "split" (List (TagT × Data) × List Bool))

set_option maxHeartbeats 0 in
def rhsEvaled : Module String (rhsType Data) := by
  precomputeTac [e| (rewriteLhsRhs DataS).output_expr, environmentRhs DataS f ] by
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq]
    rw [find?_branch_data2,find?_pure_f2,find?_split_data2,find?_merge_data2,find?_tagger_data2]
    simp [-AssocList.find?_eq]
    unfold Module.liftR Module.liftL
    dsimp
    conv =>
      pattern (occs := *) Module.connect'' _ _
      all_goals
        rw [(Module.connect''_dep_rw (h := by simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?]; rfl)
                                     (h' := by simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?]; rfl))]; rfl
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq]
    unfold Module.connect''
    dsimp
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?,AssocList.filter,-Prod.exists]

#print lhsEvaled

/--
Essentially tagger + join without internal rule
-/
@[drunfold] def NatModule.tagger_untagger_val_ghost (TagT : Type 0) [_i: DecidableEq TagT] (T : Type 0) (name := "tagger_untagger_val_ghost") : NatModule (NatModule.Named name (List TagT × AssocList TagT (T × (Nat × T)) × List (T × (Nat × T)))) :=
  { inputs := [
        -- Complete computation
        -- Models the input of the Cal + Untagger (coming from a previously tagged region)
        (0, ⟨ (TagT × T) × (Nat × T), λ (oldOrder, oldMap, oldVal) ((tag,el), r) (newOrder, newMap, newVal) =>
          -- Tag must be used, but no value ready, otherwise block:
          (tag ∈ oldOrder ∧ oldMap.find? tag = none) ∧
          newMap = oldMap.cons tag (el, r) ∧ newOrder = oldOrder ∧ newVal = oldVal ⟩),
        -- Enq a value to be tagged
        -- Models the input of the Tagger (coming from outside)
        (1, ⟨ T, λ (oldOrder, oldMap, oldVal) v (newOrder, newMap, newVal) =>
          newMap = oldMap ∧ newOrder = oldOrder ∧ newVal = oldVal.concat (v, 0, v) ⟩)
      ].toAssocList,
    outputs := [
        -- Allocate fresh tag and output with value
        -- Models the output of the Tagger
      (0, ⟨ (TagT × T) × (Nat × T), λ (oldOrder, oldMap, oldVal) ((tag, v), z) (newOrder, newMap, newVal) =>
        -- Tag must be unused otherwise block (alternatively we
        -- could an implication to say undefined behavior):
        (tag ∉ oldOrder ∧ oldMap.find? tag = none) ∧
        newMap = oldMap ∧ newOrder = oldOrder.concat tag ∧ (v, z) :: newVal = oldVal⟩),
        -- Dequeue + free tag
        -- Models the output of the Cal + Untagger
      (1, ⟨ T, λ (oldorder, oldmap, oldVal) el (neworder, newmap, newVal) =>
        -- tag must be used otherwise, but no value brought, undefined behavior:
        ∃ tag r, oldorder = tag :: neworder ∧ oldmap.find? tag = some (el, r) ∧
        newmap = oldmap.eraseAll tag ∧ newVal = oldVal ⟩),
        ].toAssocList
  }

@[drunfold] def StringModule.tagger_untagger_val_ghost TagT [DecidableEq TagT] T :=
  NatModule.tagger_untagger_val_ghost TagT T |>.stringify

def liftF2 {α β γ δ} (f : α -> β × δ) : α × (Nat × γ) -> (β × (Nat × γ)) × δ
| (a, g) =>
  let b := f a
  ((b.1, (g.1 + 1, g.2)), b.2)

def ghost_rhs
    : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i_in [type = "io"];
    o_out [type = "io"];

    tagger [typeImp = $(⟨_, StringModule.tagger_untagger_val_ghost TagT Data ⟩), type = $("tagger_untagger_val_ghost TagT " ++ DataS)];
    merge [typeImp = $(⟨_, merge ((TagT × Data) × (Nat × Data)) 2⟩), type = $("merge ((TagT × " ++ DataS ++ ") × (Nat × " ++ DataS ++ ") 2")];
    branch [typeImp = $(⟨_, branch ((TagT × Data) × (Nat × Data))⟩), type = $("branch ((TagT × " ++ DataS ++ ") × (Nat × " ++ DataS ++ ")")];
    tag_split [typeImp = $(⟨_, split ((TagT × Data) × (Nat × Data)) Bool⟩), type = $("split ((TagT × " ++ DataS ++ ") × (Nat × " ++ DataS ++ ") Bool")];
    mod [typeImp = $(⟨_, pure (liftF2 (liftF f))⟩), type = "pure (liftF2 (liftF f))"];

    i_in -> tagger [to="in2"];
    tagger -> o_out [from="out2"];

    tagger -> merge [from="out1",to="in2"];
    merge -> mod [from="out1", to="in1"];
    mod -> tag_split [from="out1", to="in1"];
    tag_split -> branch [from="out1", to="in1"];
    tag_split -> branch [from="out2", to="in2"];
    branch -> merge [from="out1", to="in1"];
    branch -> tagger [from="out2", to="in1"];
  ]

def environmentRhsGhost : IdentMap String (TModule1 String) := ghost_rhs DataS f |>.snd

def rhsGhostLower := (@ghost_rhs Unit DataS (λ _ => default) |>.1).lower.get rfl

theorem rhs_ghost_type_independent b f b₂ f₂ T [Inhabited b] [Inhabited b₂]
  : (@ghost_rhs b T f).fst = (@ghost_rhs b₂ T f₂).fst := by rfl

@[drcompute] theorem find?_branch_data3 : (Batteries.AssocList.find? ("branch ((TagT × " ++ DataS ++ ") × (Nat × " ++ DataS ++ ")") (environmentRhsGhost DataS f)) = .some ⟨_, branch ((TagT × Data) × (Nat × Data))⟩ := sorry
@[drcompute] theorem find?_pure_f3 : (Batteries.AssocList.find? "pure (liftF2 (liftF f))" (environmentRhsGhost DataS f)) = .some ⟨_, pure (liftF2 (γ := Data) (liftF (γ := TagT) f))⟩ := sorry
@[drcompute] theorem find?_merge_data3 : (Batteries.AssocList.find? ("merge ((TagT × " ++ DataS ++ ") × (Nat × " ++ DataS ++ ") 2") (environmentRhsGhost DataS f)) = .some ⟨_, merge ((TagT × Data) × (Nat × Data)) 2⟩ := sorry
@[drcompute] theorem find?_split_data3 : (Batteries.AssocList.find? ("split ((TagT × " ++ DataS ++ ") × (Nat × " ++ DataS ++ ") Bool") (environmentRhsGhost DataS f)) = .some ⟨_, split ((TagT × Data) × (Nat × Data)) Bool⟩ := sorry
@[drcompute] theorem find?_tagger_data3 : (Batteries.AssocList.find? ("tagger_untagger_val_ghost TagT " ++ DataS) (environmentRhsGhost DataS f)) = .some ⟨_, StringModule.tagger_untagger_val_ghost TagT Data ⟩ := sorry

variable (Data) in
abbrev rhsGhostType :=
        (NatModule.Named "pure" (List (((TagT × Data) × ℕ × Data) × Bool)) ×
          NatModule.Named "branch" (List ((TagT × Data) × ℕ × Data) × List Bool) ×
            NatModule.Named "merge" (List ((TagT × Data) × ℕ × Data)) ×
              NatModule.Named "tagger_untagger_val_ghost" (List TagT × AssocList TagT (Data × (Nat × Data)) × List (Data × ℕ × Data)) ×
                NatModule.Named "split" (List ((TagT × Data) × ℕ × Data) × List Bool))

set_option maxHeartbeats 0 in
def rhsGhostEvaled : Module String (rhsGhostType Data) := by
  precomputeTac [e| rhsGhostLower DataS, environmentRhsGhost DataS f ] by
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq]
    rw [find?_branch_data3,find?_pure_f3,find?_split_data3,find?_merge_data3,find?_tagger_data3]
    simp [-AssocList.find?_eq]
    unfold Module.liftR Module.liftL
    dsimp
    conv =>
      pattern (occs := *) Module.connect'' _ _
      all_goals
        rw [(Module.connect''_dep_rw (h := by simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?]; rfl)
                                     (h' := by simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?]; rfl))]; rfl
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq]
    unfold Module.connect''
    dsimp
    simp [Batteries.AssocList.find?, -Prod.exists]



def apply (n : Nat) (i : Data) : Data × Bool :=
match n with
| 0 => f i
| n' + 1 => f (apply n' i).fst


def iterate (i: Data) (n : Nat) (i': Data) : Prop :=
  (∀ m, m < n -> (apply f m i).snd = true) ∧ apply f n i = (i', false)

#print rhsGhostType

inductive state_relation : rhsGhostType Data -> Prop where
| intros : ∀ (s :  rhsGhostType Data) x_merge x_module x_branchD x_branchB x_tagT x_tagM x_tagD x_splitD x_splitB x_branchT x_branchF x_splitT x_splitF x_moduleT x_moduleF,
  ⟨ x_module, ⟨x_branchD, x_branchB⟩, x_merge, ⟨x_tagT, x_tagM, x_tagD ⟩, ⟨x_splitD, x_splitB⟩⟩ = s ->
  ∀ elem n i', elem ∈ x_merge -> iterate f elem.2.2 n i' -> elem.2.1 ≥ 0 ∧ elem.2.1 - 1 < n ->
  List.map Prod.fst (List.filter (fun x => x.2 == true) (List.zip x_branchD x_branchB)) = x_branchT ->
  List.map Prod.fst (List.filter (fun x => x.2 == false) (List.zip x_branchD x_branchB)) = x_branchF->
  List.map Prod.fst (List.filter (fun x => x.2 == true) (List.zip x_splitD x_splitB)) = x_splitT ->
  List.map Prod.fst (List.filter (fun x => x.2 == false) (List.zip x_splitD x_splitB)) = x_splitF ->
  List.map Prod.fst (List.filter (fun x => x.2 == true) (x_module)) = x_moduleT ->
  List.map Prod.fst (List.filter (fun x => x.2 == false) (x_module)) = x_moduleF ->
 ( ∀ elem n i', elem ∈ x_moduleT ++ x_splitT ++ x_branchT -> iterate f elem.2.2 n i' -> elem.2.1 > 0 ∧ elem.2.1-1 < n) ->
  (∀ elem n i', elem ∈ x_moduleF ++ x_splitF ++ x_branchF -> iterate f elem.2.2 n i' -> elem.2.1 > 0 ∧ elem.2.1-1 = n) ->
  --∀ elem n i', elem ∈ x_module.map Prod.fst -> iterate f elem.2.2 n i' -> x_module = [(apply f elem.2.1 elem.2.2)] ->



--  ( ∀ n k i',
--     iterate f i_in n i' ->
--     k ≤ n ->
--     (k < n -> x_module = [(apply f k i_in )] ∧ x_module.map Prod.snd = [true]) ->
--     (k = n -> x_module = [(apply f n i_in )] ∧ x_module.map Prod.snd = [false]) ->
--     (x_splitB = [true] -> k < n ∧  x_splitD = [(apply f k i_in )].map Prod.fst) ->
--     (x_splitB = [false] -> k = n ∧  x_splitD = [(apply f k i_in )].map Prod.fst)) ->
  state_relation s













end Proof

end DataflowRewriter.LoopRewrite
