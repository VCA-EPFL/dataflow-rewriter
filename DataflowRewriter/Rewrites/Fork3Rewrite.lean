/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ayatallah Elakhras
-/

import DataflowRewriter.Rewriter
import DataflowRewriter.ExprHighElaborator

namespace DataflowRewriter.ReduceSplitJoin

open StringModule

def matcher (g : ExprHigh String) : RewriteResult (List String × List String) := do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
      if s.isSome then return s

      unless "fork".isPrefixOf typ do return none

      let l := typ.splitOn " "
      unless l.getLast? = .some "3" do return none
      let forkType := l.drop 1 |>.dropLast |> " ".intercalate

      return some ([inst], [forkType])
    ) none | throw .done
  return list

def lhs (T : Type) (Tₛ : String) : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i [type = "io"];
    o1 [type = "io"];
    o2 [type = "io"];
    o3 [type = "io"];

    fork [typeImp = $(⟨_, fork T 3⟩), type = $("fork " ++ Tₛ ++ " 3")];

    i -> fork [to="in1"];
    fork -> o1 [from="out1"];
    fork -> o2 [from="out2"];
    fork -> o3 [from="out3"];
  ]

def lhs_extract T₁ := (lhs Unit T₁).fst.extract ["fork"] |>.get rfl

-- #eval IO.print ((lhs Unit "T").fst)

theorem lhs_type_independent a c T₁ : (lhs a T₁).fst = (lhs c T₁).fst := by rfl

theorem double_check_empty_snd T₁ : (lhs_extract T₁).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower T₁ := lhs_extract T₁ |>.fst.lower.get rfl

def rhs (T : Type) (Tₛ : String) : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i [type = "io"];
    o1 [type = "io"];
    o2 [type = "io"];
    o3 [type = "io"];

    fork1 [typeImp = $(⟨_, fork T 2⟩), type = $("fork " ++ Tₛ ++ " 2")];
    fork2 [typeImp = $(⟨_, fork T 2⟩), type = $("fork " ++ Tₛ ++ " 2")];

    i -> fork1 [to="in1"];
    fork1 -> fork2 [from="out2", to="in1"];

    fork1 -> o1 [from="out1"];
    fork2 -> o2 [from="out1"];
    fork2 -> o3 [from="out2"];
  ]

def rhsLower T₁ := (rhs Unit T₁).fst.lower.get rfl

-- #eval IO.print ((rhs Unit "T").fst)

theorem rhs_type_independent a c T₁ : (rhs a T₁).fst = (rhs c T₁).fst := by rfl

def rewrite : Rewrite String :=
  { abstractions := [],
    pattern := matcher,
    rewrite := λ | [T₁] => pure ⟨lhsLower T₁, rhsLower T₁⟩ | _ => failure
    name := .some "fork-3"
  }

end DataflowRewriter.ReduceSplitJoin
