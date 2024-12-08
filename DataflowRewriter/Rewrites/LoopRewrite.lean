/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.Rewriter
import DataflowRewriter.ExprHighElaborator

namespace DataflowRewriter.JoinRewrite

open StringModule

instance : MonadExcept IO.Error RewriteResult where
  throw e := throw <| .error <| toString e
  tryCatch m h := throw (.error "Cannot catch IO.Error")

unsafe def matcher (g : ExprHigh String) : RewriteResult (List String) := do
  let mergeId ← ofExcept <| unsafeIO do
    -- read file or whatever else one wants to do, then return the mux instance
    -- name
    return "mux"
  return [mergeId]

def makeMockModule {S} (mockIn1 mockOut1 : Type)
    (mockIn1Rule : S → mockIn1 → S → Prop)
    (mockOut1Rule : S → mockOut1 → S → Prop) : Module String S :=
  { inputs := [(⟨.top, "inp0"⟩, ⟨mockIn1, mockIn1Rule⟩)].toAssocList
  , outputs := [(⟨.top, "out0"⟩, ⟨mockOut1, mockOut1Rule⟩)].toAssocList
  , internals := []
  }

def lhs (S T:Type) (TagT:Type) [DecidableEq TagT]
      (inRule : S → TagT × T → S → Prop)
      (outRule : S → TagT × T × Bool → S → Prop)
      -- (outRule : S → T' → S → Prop)
    : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i_in [type = "io"];
    o_out [type = "io"];

    mux [type = $(⟨_, mux T⟩)];
    condition_fork [type = $(⟨_, fork Bool 2⟩)];
    branch [type = $(⟨_, branch T⟩)];
    inside_tagger [type = $(⟨_, tagger_untagger_val TagT T (T × Bool)⟩)];
    tag_split [type = $(⟨_, split T Bool⟩)];
    mod [type = $(⟨_, makeMockModule (TagT × T) (TagT × (T × Bool)) inRule outRule⟩)];
    loop_init [type = $(⟨_, init Bool false⟩)];
    bag [type = $(⟨_, bag T⟩)];

    loop_init -> mux [out="out0", inp="inp2"];
    condition_fork -> loop_init [out="out1", inp="inp0"];
    condition_fork -> branch [out="out0", inp="inp1"];
    inside_tagger -> mod [out="out0", inp="inp0"];
    mod -> inside_tagger [out="out0", inp="inp0"];
    inside_tagger -> tag_split [out="out1", inp="inp0"];
    tag_split -> branch [out="out0", inp="inp0"];
    tag_split -> condition_fork [out="out1", inp="inp0"];
    mux -> inside_tagger [out="out0", inp="inp1"];
    branch -> mux [out="out0", inp="inp0"];
    i_in -> mux [inp="inp1"];
    branch -> bag [out="out1", inp="inp0"];
    bag -> o_out [out="out0"];
  ]

-- #eval lhs Unit Unit Unit (λ _ _ _ => False) (λ _ _ _ => False) |>.1 |> IO.print

def lhs_extract := lhs Unit Unit Unit (λ _ _ _ => False) (λ _ _ _ => False) |>.1
  |>.extract ["mux", "condition_fork", "branch", "inside_tagger", "tag_split", "mod", "loop_init", "bag"]
  |>.get rfl

theorem double_check_empty_snd : lhs_extract.snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := lhs_extract.fst.lower.get rfl

def rhs (S T:Type) (TagT:Type) [DecidableEq TagT]
      (inRule : S → TagT × T → S → Prop)
      (outRule : S → TagT × T × Bool → S → Prop)
      -- (outRule : S → T' → S → Prop)
    : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i_in [type = "io"];
    o_out [type = "io"];

    merge [type = $(⟨_, merge T 2⟩)];
    condition_fork [type = $(⟨_, fork Bool 2⟩)];
    branch [type = $(⟨_, branch T⟩)];
    inside_tagger [type = $(⟨_, tagger_untagger_val TagT T (T × Bool)⟩)];
    tag_split [type = $(⟨_, split T Bool⟩)];
    mod [type = $(⟨_, makeMockModule (TagT × T) (TagT × (T × Bool)) inRule outRule⟩)];
    loop_init [type = $(⟨_, init Bool false⟩)];

    condition_fork -> loop_init [out="out1", inp="inp0"];
    condition_fork -> branch [out="out0", inp="inp1"];
    inside_tagger -> mod [out="out0", inp="inp0"];
    mod -> inside_tagger [out="out0", inp="inp0"];
    inside_tagger -> tag_split [out="out1", inp="inp0"];
    tag_split -> branch [out="out0", inp="inp0"];
    tag_split -> condition_fork [out="out1", inp="inp0"];
    merge -> inside_tagger [out="out0", inp="inp1"];
    branch -> merge [out="out0", inp="inp0"];
    i_in -> merge [inp="inp1"];
    branch -> o_out [out="out1"];
  ]

def rhsLower := (rhs Unit Unit Unit (λ _ _ _ => False) (λ _ _ _ => False) |>.1).lower.get rfl

def rewrite : Rewrite String :=
  { abstractions := [],
    pattern := unsafe matcher,
    input_expr := lhsLower,
    output_expr := rhsLower }

end DataflowRewriter.JoinRewrite
