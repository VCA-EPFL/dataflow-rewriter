/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.Rewriter
import DataflowRewriter.ExprHighElaborator

namespace DataflowRewriter.ForkPure

open StringModule

variable (T₁ T₂ : Type)
variable (f : T₁ → T₂)
variable (S₁ S₂ : String)

def matcher (g : ExprHigh String) : RewriteResult (List String × List String) := do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
       if s.isSome then return s
       unless "pure".isPrefixOf typ do return none

       let (.some p) := followOutput g inst "out1" | return none
       unless "fork".isPrefixOf p.typ do return none

       let (.some t1) := p.typ.splitOn |>.get? 1 | return none
       let (.some jt1) := typ.splitOn |>.get? 1 | return none
       let (.some jt2) := typ.splitOn |>.get? 2 | return none

       unless t1 = jt2 do throw (.error s!"{inst} :: {p.inst}")

       return some ([inst, p.inst], [jt1, jt2])
    ) none | MonadExceptOf.throw RewriteError.done
  return list

def lhs : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i [type = "io"];
    o1 [type = "io"];
    o2 [type = "io"];

    pure [typeImp = $(⟨_, StringModule.pure f⟩), type = $(s!"pure {S₁} {S₂}")];
    fork [typeImp = $(⟨_, fork T₂ 2⟩), type = $(s!"fork {S₂} 2")];

    i -> pure [to="in1"];
    pure -> fork [from="out1",to="in1"];
    fork -> o1 [from="out1"];
    fork -> o2 [from="out2"];
  ]

def lhs_extract := (lhs Unit Unit (λ _ => default) S₁ S₂).fst.extract ["pure", "fork"] |>.get rfl

theorem double_check_empty_snd : (lhs_extract S₁ S₂).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := (lhs_extract S₁ S₂).fst.lower.get rfl

def rhs : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i [type = "io"];
    o1 [type = "io"];
    o2 [type = "io"];

    fork [typeImp = $(⟨_, fork T₁ 2⟩), type = $(s!"fork {S₁} 2")];
    pure1 [typeImp = $(⟨_, StringModule.pure f⟩), type = $(s!"pure {S₁} {S₂}")];
    pure2 [typeImp = $(⟨_, StringModule.pure f⟩), type = $(s!"pure {S₁} {S₂}")];

    i -> fork [to="in1"];
    fork -> pure1 [from="out1",to="in1"];
    fork -> pure2 [from="out2",to="in1"];
    pure1 -> o1 [from="out1"];
    pure2 -> o2 [from="out1"];
  ]

def rhsLower := (rhs Unit Unit (λ _ => default) S₁ S₂).fst.lower.get rfl

def rewrite : Rewrite String :=
  { abstractions := [],
    pattern := matcher,
    rewrite := λ | [S₁, S₂] => .some ⟨lhsLower S₁ S₂, rhsLower S₁ S₂⟩ | _ => failure,
    name := "fork-pure"
  }

end DataflowRewriter.ForkPure
