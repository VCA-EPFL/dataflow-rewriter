/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.Rewriter
import DataflowRewriter.ExprHighElaborator

namespace DataflowRewriter.JoinAssocR

open StringModule

def matcher (g : ExprHigh String) : RewriteResult (List String × List String) := sorry

def lhs (T₁ T₂ T₃ : Type) (S₁ S₂ S₃ : String) : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i_0 [type = "io"];
    i_1 [type = "io"];
    i_2 [type = "io"];
    o_out [type = "io"];

    join1 [typeImp = $(⟨_, join T₂ T₃⟩), type = $("join " ++ S₂ ++  " " ++ S₃)];
    join2 [typeImp = $(⟨_, join T₁ (T₂ × T₃)⟩), type = $("join " ++ S₁ ++ " (" ++ S₂ ++ " × " ++ S₃ ++ ")")];

    i_0 -> join1 [to = "in1"];
    i_1 -> join1 [to = "in2"];
    i_2 -> join2 [to = "in2"];

    join1 -> join2 [from = "out1", to = "in1"];

    join2 -> o_out [from = "out1"];
  ]

def lhs_extract S₁ S₂ S₃ := (lhs Unit Unit Unit S₁ S₂ S₃).fst.extract ["join1", "join2"] |>.get rfl

theorem double_check_empty_snd S₁ S₂ S₃ : (lhs_extract S₁ S₂ S₃).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower S₁ S₂ S₃ := (lhs_extract S₁ S₂ S₃).fst.lower.get rfl

def rhs (T₁ T₂ T₃ : Type) (S₁ S₂ S₃ : String) : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i_0 [type = "io"];
    i_1 [type = "io"];
    i_2 [type = "io"];
    o_out [type = "io"];

    join2 [typeImp = $(⟨_, join T₂ T₃⟩), type = $("join " ++ S₂ ++ " " ++ S₃)];
    join1 [typeImp = $(⟨_, join T₁ (T₂ × T₃)⟩), type = $("join " ++ S₁ ++ " (" ++ S₂ ++ " × " ++ S₃ ++ ")")];
    pure [typeImp = $(⟨_, StringModule.pure (λ ((a, b, c) : T₁ × T₂ × T₃) => ((a, b), c))⟩),
          type = $("pure  (λ ((a, b, c) : " ++ S₁ ++ " × " ++ S₂ ++ " × " ++ S₃ ++ ") => ((a, b), c)")];

    i_1 -> join2 [to = "in1"];
    i_2 -> join2 [to = "in2"];
    i_0 -> join1 [to = "in1"];

    join2 -> join1 [from = "out1", to = "in2"];
    join1 -> pure [from = "out1", to = "in1"];

    pure -> o_out [from = "out1"];
  ]

def rhsLower S₁ S₂ S₃ := (rhs Unit Unit Unit S₁ S₂ S₃).fst.lower.get rfl

def rewrite : Rewrite String :=
  { abstractions := [],
    pattern := matcher,
    rewrite := λ | [S₁, S₂, S₃] => pure ⟨lhsLower S₁ S₂ S₃, rhsLower S₁ S₂ S₃⟩ | _ => failure
    }

end DataflowRewriter.JoinAssocR
