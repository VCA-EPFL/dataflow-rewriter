/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ayatallah Elakhras
-/


-- The order of the operation of combineMux and combineBranch is not consistent somehow;
-- therefore, we do not necessarily end up with Split -> Join, but instead end with Split -> Split -> Join -> Join
-- Temporarily, until we figure out how to make the order of applying the combine rewrites consistent, I'm adding this rewrite to reduce the complicated pattern

import DataflowRewriter.Rewriter
import DataflowRewriter.ExprHighElaborator

namespace DataflowRewriter.ReduceSplitJoin

open StringModule

def extractLastWordAfterJoin (s : String) : String :=
  match s.drop 5 |>.splitOn " " with
  | []      => ""
  | xs      => xs.getLastD ""  -- Get the last word, or return "" if the list is empty

  -- match s.drop 5 |>.splitOn " " with
  -- | []      => ""
  -- | x :: _  => x

def matcher (g : ExprHigh String) : RewriteResult (List String × List String) := do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
      if s.isSome then return s
        unless String.isPrefixOf "split" typ do return none
      let (.some split_1_out_join_1) := followOutput g inst "out1" | return none
      let (.some split_1_out_split_2) := followOutput g inst "out2" | return none

      unless String.isPrefixOf "join" split_1_out_join_1.typ && String.isPrefixOf "split" split_1_out_split_2.typ do return none

      let (.some split_2_out_join_1) := followOutput g split_1_out_split_2.inst "out1" | return none
      let (.some split_2_out_join_2) := followOutput g split_1_out_split_2.inst "out2" | return none

      unless String.isPrefixOf "join" split_2_out_join_1.typ && split_2_out_join_1.inst == split_1_out_join_1.inst  do return none

      let (.some join_1_out_join_2) := followOutput g split_2_out_join_1.inst "out1" | return none

      unless String.isPrefixOf "join" join_1_out_join_2.typ && String.isPrefixOf "join" split_2_out_join_2.typ && join_1_out_join_2.inst == split_2_out_join_2.inst  do return none

      return some ([join_1_out_join_2.inst, split_1_out_join_1.inst, split_1_out_split_2.inst, inst], [extractLastWordAfterJoin split_1_out_join_1.typ, extractLastWordAfterJoin join_1_out_join_2.typ])
    ) none | throw .done
  return list

def lhs (T T' : Type) (Tₛ T'ₛ : String) : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i [type = "io"];
    o [type = "io"];

    split1 [typeImp = $(⟨_, split T T'⟩), type = $("split " ++ Tₛ ++ " (" ++ T'ₛ ++ ")")];
    split2 [typeImp = $(⟨_, split T T⟩), type = $("split " ++ Tₛ ++ " " ++ Tₛ)];
    join1 [typeImp = $(⟨_, join T T⟩), type = $("join " ++ Tₛ ++ " " ++ Tₛ)];
    join2 [typeImp = $(⟨_, join T T'⟩), type = $("join " ++ Tₛ ++ " (" ++ T'ₛ ++ ")")];

    i -> split1 [to="in1"];
    split1 -> join1 [from="out1", to="in1"];
    split1 -> split2 [from="out2", to="in1"];

    split2 -> join1 [from="out1", to="in2"];
    split2 -> join2 [from="out2", to="in2"];

    join1 -> join2 [from="out2", to="in2"];

    join2 -> o [from="out1"];
  ]

def lhs_extract T₁ T₂ := (lhs Unit Unit T₁ T₂).fst.extract ["join2", "join1", "split2", "split1"] |>.get rfl

theorem lhs_type_independent a b c d T₁ T₂ : (lhs a b T₁ T₂).fst = (lhs c d T₁ T₂).fst := by rfl

theorem double_check_empty_snd T₁ T₂ : (lhs_extract T₁ T₂).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower T₁ T₂ := lhs_extract T₁ T₂ |>.fst.lower.get rfl

def rhs (T T' : Type) (Tₛ T'ₛ : String) : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i [type = "io"];
    o [type = "io"];

    queue [typeImp = $(⟨_, queue T⟩), type = $("queue" ++ " " ++ Tₛ)];

    i -> queue [to="in1"];
    queue -> o [from="out1"];
  ]

def rhsLower T₁ T₂ := (rhs Unit Unit T₁ T₂).fst.lower.get rfl

#eval IO.print ((rhs Unit Unit "T" "T'").fst)

theorem rhs_type_independent a b c d T₁ T₂ : (rhs a b T₁ T₂).fst = (rhs c d T₁ T₂).fst := by rfl

def rewrite : Rewrite String :=
  { abstractions := [],
    pattern := matcher,
    rewrite := λ l => do
      let T₁ ← l.get? 0
      let T₂ ← l.get? 1
      return ⟨lhsLower T₁ T₂, rhsLower T₁ T₂⟩
    name := .some "reduce-split-join"
  }

end DataflowRewriter.ReduceSplitJoin
