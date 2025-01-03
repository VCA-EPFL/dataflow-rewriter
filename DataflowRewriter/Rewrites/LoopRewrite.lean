/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.Rewriter
import DataflowRewriter.ExprHighElaborator

namespace DataflowRewriter.LoopRewrite

open StringModule

instance : MonadExcept IO.Error RewriteResult where
  throw e := throw <| .error <| toString e
  tryCatch m h := throw (.error "Cannot catch IO.Error")

unsafe def matcher (T₁ T₂ : String) (g : ExprHigh String) : RewriteResult (List String) := do
  let mergeId ← ofExcept <| unsafeIO do
    -- read file or whatever else one wants to do, then return the mux instance
    -- name
    return "mux"
  return [mergeId]

def makeMockModule {S} (mockIn1 mockOut1 : Type)
    (mockIn1Rule : S → mockIn1 → S → Prop)
    (mockOut1Rule : S → mockOut1 → S → Prop) : Module String S :=
  { inputs := [(⟨.top, "in1"⟩, ⟨mockIn1, mockIn1Rule⟩)].toAssocList
  , outputs := [(⟨.top, "out1"⟩, ⟨mockOut1, mockOut1Rule⟩)].toAssocList
  , internals := []
  }

def lhs (S T TagT : Type) [DecidableEq TagT]
      (Tₛ TagTₛ : String)
      (inRule : S → TagT × T → S → Prop)
      (outRule : S → TagT × T × Bool → S → Prop)
      -- (outRule : S → T' → S → Prop)
    : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i_in [type = "io"];
    o_out [type = "io"];

    mux [typeImp = $(⟨_, mux T⟩), type = $("mux " ++ Tₛ)];
    condition_fork [typeImp = $(⟨_, fork Bool 2⟩), type = "fork Bool 2"];
    branch [typeImp = $(⟨_, branch T⟩), type = $("branch " ++ Tₛ)];
    inside_tagger [typeImp = $(⟨_, tagger_untagger_val TagT T (T × Bool)⟩), type = $("tagger_untagger_val " ++ TagTₛ ++ " " ++ Tₛ ++ " (" ++ Tₛ ++ " × Bool)")];
    tag_split [typeImp = $(⟨_, split T Bool⟩), type = $("split " ++ Tₛ ++ " Bool")];
    mod [typeImp = $(⟨_, makeMockModule (TagT × T) (TagT × (T × Bool)) inRule outRule⟩), type = "M"];
    loop_init [typeImp = $(⟨_, init Bool false⟩), type = "init Bool false"];
    bag [typeImp = $(⟨_, bag T⟩), type = $("bag " ++ Tₛ)];

    loop_init -> mux [from="out1", to="in1"];
    condition_fork -> loop_init [from="out2", to="in1"];
    condition_fork -> branch [from="out1", to="in2"];
    inside_tagger -> mod [from="out1", to="in1"];
    mod -> inside_tagger [from="out1", to="in1"];
    inside_tagger -> tag_split [from="out2", to="in1"];
    tag_split -> branch [from="out1", to="in1"];
    tag_split -> condition_fork [from="out2", to="in1"];
    mux -> inside_tagger [from="out1", to="in2"];
    branch -> mux [from="out1", to="in2"];
    i_in -> mux [to="in3"];
    branch -> bag [from="out2", to="in1"];
    bag -> o_out [from="out1"];
  ]

#eval IO.print ((lhs Unit Unit Unit "T" "T'" (λ _ _ _ => False) (λ _ _ _ => False)).fst)

-- #eval lhs Unit Unit Unit (λ _ _ _ => False) (λ _ _ _ => False) |>.1 |> IO.print

def lhs_extract T₁ T₂ := lhs Unit Unit Unit T₁ T₂ (λ _ _ _ => False) (λ _ _ _ => False) |>.1
  |>.extract ["mux", "condition_fork", "branch", "inside_tagger", "tag_split", "mod", "loop_init", "bag"]
  |>.get rfl

theorem double_check_empty_snd T₁ T₂: (lhs_extract T₁ T₂).snd = ExprHigh.mk ∅ ∅ := by rfl

theorem lhs_type_independent a b c e f a₂ b₂ c₂ e₂ f₂ T₁ T₂ [DecidableEq c] [DecidableEq c₂]
  : (lhs a b c T₁ T₂ e f).fst = (lhs a₂ b₂ c₂ T₁ T₂ e₂ f₂).fst := by rfl

def lhsLower T₁ T₂ := (lhs_extract T₁ T₂).fst.lower.get rfl

def rhs (S T TagT : Type) [DecidableEq TagT]
      (Tₛ TagTₛ : String)
      (inRule : S → TagT × T → S → Prop)
      (outRule : S → TagT × T × Bool → S → Prop)
      -- (outRule : S → T' → S → Prop)
    : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i_in [type = "io"];
    o_out [type = "io"];

    merge [typeImp = $(⟨_, merge T 2⟩), type = $("merge " ++ Tₛ ++ " 2")];
    condition_fork [typeImp = $(⟨_, fork Bool 2⟩), type = "fork Bool 2"];
    branch [typeImp = $(⟨_, branch T⟩), type = $("branch " ++ Tₛ)];
    inside_tagger [typeImp = $(⟨_, tagger_untagger_val TagT T (T × Bool)⟩), type = $("tagger_untagger_val " ++ TagTₛ ++ " " ++ Tₛ ++ " (" ++ Tₛ ++ " × Bool)")];
    tag_split [typeImp = $(⟨_, split T Bool⟩), type = $("split " ++ Tₛ ++ " Bool")];
    mod [typeImp = $(⟨_, makeMockModule (TagT × T) (TagT × (T × Bool)) inRule outRule⟩), type = "M"];

    tag_split -> branch [from="out2", to="in2"];
    inside_tagger -> mod [from="out1", to="in1"];
    mod -> inside_tagger [from="out1", to="in1"];
    inside_tagger -> tag_split [from="out2", to="in1"];
    tag_split -> branch [from="out1", to="in1"];
    merge -> inside_tagger [from="out1", to="in2"];
    branch -> merge [from="out1", to="in1"];
    i_in -> merge [to="in2"];
    branch -> o_out [from="out2"];
  ]

def rhsLower T₁ T₂ := (rhs Unit Unit Unit T₁ T₂ (λ _ _ _ => False) (λ _ _ _ => False) |>.1).lower.get rfl

theorem rhs_type_independent a b c e f a₂ b₂ c₂ e₂ f₂ T₁ T₂ [DecidableEq c] [DecidableEq c₂]
  : (rhs a b c T₁ T₂ e f).fst = (rhs a₂ b₂ c₂ T₁ T₂ e₂ f₂).fst := by rfl

#eval IO.print ((rhs Unit Unit Unit "T" "T'" (λ _ _ _ => False) (λ _ _ _ => False)).fst)

def rewrite (T₁ T₂ : String) : Rewrite String :=
  { abstractions := [],
    pattern := unsafe matcher T₁ T₂,
    input_expr := lhsLower T₁ T₂,
    output_expr := rhsLower T₁ T₂ }

end DataflowRewriter.LoopRewrite
