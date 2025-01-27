/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.Rewriter
import DataflowRewriter.ExprHighElaborator

namespace DataflowRewriter.LoopRewrite

open StringModule

local instance : MonadExcept IO.Error RewriteResult where
  throw e := throw <| .error <| toString e
  tryCatch m h := throw (.error "Cannot catch IO.Error")

unsafe def matcher (g : ExprHigh String) : RewriteResult (List String × List String) := do
  let merges ← ofExcept <| unsafeIO do
    -- Here you can run an arbitrary command with arguments, where stdout will be passed to `result`.  This can be used
    -- to implement the matcher completely externally.
    let result ← IO.Process.run { cmd := "echo", args := #["merge1, merge2, merge3"] }
    return result.trim.splitOn ", "
  return (merges, [])

-- It can then be tested using the below command
#eval (matcher [graph| merge1 [type = "merge"]; merge2 [type = "merge"];
               merge1 -> merge2 [from = "out1", to = "in1"]; ] /- <--- replace this with the input graph to test with (as an ExprHigh). -/
       ).run' default

def lhs (T : Type) [Inhabited T] (Tₛ : String) (f : T → T × Bool)
      : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i_in [type = "io"];
    o_out [type = "io"];

    mux [typeImp = $(⟨_, mux T⟩), type = $("mux " ++ Tₛ)];
    condition_fork [typeImp = $(⟨_, fork Bool 2 ⟩), type = "fork Bool 2"];
    branch [typeImp = $(⟨_, branch T⟩), type = $("branch " ++ Tₛ)];
    tag_split [typeImp = $(⟨_, split T Bool⟩), type = $("split " ++ Tₛ ++ " Bool")];
    mod [typeImp = $(⟨_, pure f⟩), type = "pure f"];
    loop_init [typeImp = $(⟨_, init Bool false⟩), type = "init Bool false"];
    bag [typeImp = $(⟨_, bag T⟩), type = $("bag " ++ Tₛ)];
    queue [typeImp = $(⟨_, queue T⟩), type = $("queue " ++ Tₛ)];

    i_in -> mux [to="in3"];
    bag -> o_out [from="out1"];

    loop_init -> mux [from="out1", to="in1"];
    condition_fork -> loop_init [from="out2", to="in1"];
    condition_fork -> branch [from="out1", to="in2"];
    mod -> tag_split [from="out1", to="in1"];
    tag_split -> branch [from="out1", to="in1"];
    tag_split -> condition_fork [from="out2", to="in1"];
    mux -> mod [from="out1", to="in1"];
    branch -> queue [from="out1", to="in1"];
    queue -> mux [from="out1", to="in2"];
    branch -> bag [from="out2", to="in1"];
  ]

#eval IO.print ((lhs Unit "T" (λ _ => default)).fst)

-- #eval lhs Unit Unit Unit (λ _ _ _ => False) (λ _ _ _ => False) |>.1 |> IO.print

def lhs_extract T := lhs Unit T (λ _ => default) |>.1
  |>.extract ["mux", "condition_fork", "branch", "tag_split", "mod", "loop_init", "bag"]
  |>.get rfl

theorem double_check_empty_snd T: (lhs_extract T).snd = ExprHigh.mk ∅ ∅ := by rfl

theorem lhs_type_independent a f a₂ f₂ T
        [Inhabited a] [Inhabited a₂]
  : (lhs a T f).fst = (lhs a₂ T f₂).fst := by rfl

def lhsLower T := (lhs_extract T).fst.lower.get rfl

abbrev TagT := Nat

def liftF {α β γ δ} (f : α -> β × δ) : γ × α -> (γ × β) × δ | (g, a) => ((g, f a |>.fst), f a |>.snd)

def rhs (T : Type) [Inhabited T] (Tₛ : String) (f : T → T × Bool)
    : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i_in [type = "io"];
    o_out [type = "io"];

    tagger [typeImp = $(⟨_, tagger_untagger_val TagT T T ⟩), type = $("tagger_untagger_val TagT " ++ Tₛ ++ " " ++ Tₛ)];
    merge [typeImp = $(⟨_, merge (TagT × T) 2⟩), type = $("merge (TagT × " ++ Tₛ ++ ") 2")];
    branch [typeImp = $(⟨_, branch (TagT × T)⟩), type = $("branch (TagT × " ++ Tₛ ++ ")")];
    tag_split [typeImp = $(⟨_, split (TagT × T) Bool⟩), type = $("split (TagT × " ++ Tₛ ++ ") Bool")];
    mod [typeImp = $(⟨_, pure (liftF f)⟩), type = "pure (liftF f)"];

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

def rhsLower T := (rhs Unit T (λ _ => default) |>.1).lower.get rfl

theorem rhs_type_independent b f b₂ f₂ T [Inhabited b] [Inhabited b₂]
  : (rhs b T f).fst = (rhs b₂ T f₂).fst := by rfl

#eval IO.print ((rhs Unit "T" (λ _ => default)).fst)

def rewrite : Rewrite String :=
  { abstractions := [],
    pattern := unsafe matcher,
    rewrite := λ l => do
      let T ← l.get? 0
      return ⟨lhsLower T, rhsLower T⟩
    name := .some "loop-rewrite"
  }

end DataflowRewriter.LoopRewrite
