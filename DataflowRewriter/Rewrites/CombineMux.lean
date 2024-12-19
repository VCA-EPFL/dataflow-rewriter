/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.Rewriter
import DataflowRewriter.ExprHighElaborator

namespace DataflowRewriter.CombineMux

open StringModule

def matcher (T T' : String) (g : ExprHigh String) : RewriteResult (List String) := do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
      if s.isSome then return s
      unless typ = "fork Bool 2" do return none
      let (.some mux_nn) := followOutput g inst "out0" | return none
      let (.some mux_nn') := followOutput g inst "out1" | return none
      unless mux_nn.typ = "mux " ++ T && mux_nn.inputPort = "inp2" do return none
      unless mux_nn'.typ = "mux " ++ T' && mux_nn'.inputPort = "inp2" do return none
      return some [mux_nn.inst, mux_nn'.inst, inst]
    ) none | throw .done
  return list

def lhs (T T' : Type) (Tₛ T'ₛ : String) : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    b1_t_i [type = "io"];
    b1_f_i [type = "io"];
    b2_t_i [type = "io"];
    b2_f_i [type = "io"];
    cond_i [type = "io"];
    b1_o [type = "io"];
    b2_o [type = "io"];

    mux1 [typeImp = $(⟨_, mux T⟩), type = $("mux " ++ Tₛ)];
    mux2 [typeImp = $(⟨_, mux T'⟩), type = $("mux " ++ T'ₛ)];
    condFork [typeImp = $(⟨_, fork Bool 2⟩), type = "fork Bool 2"];

    mux1 -> b1_o [out="out0"];
    mux2 -> b2_o [out="out0"];

    cond_i -> condFork [inp="inp0"];
    b1_t_i -> mux1 [inp="inp0"];
    b1_f_i -> mux1 [inp="inp1"];
    b2_t_i -> mux2 [inp="inp0"];
    b2_f_i -> mux2 [inp="inp1"];

    condFork -> mux1 [out="out0", inp="inp2"];
    condFork -> mux2 [out="out1", inp="inp2"];
  ]

-- #reduce lhs Unit Unit "H" "Y"

def lhs_extract T₁ T₂ := (lhs Unit Unit T₁ T₂).fst.extract ["mux1", "mux2", "condFork"] |>.get rfl

theorem lhs_type_independent a b c d T₁ T₂ : (lhs a b T₁ T₂).fst = (lhs c d T₁ T₂).fst := by rfl

theorem double_check_empty_snd T₁ T₂ : (lhs_extract T₁ T₂).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower T₁ T₂ := lhs_extract T₁ T₂ |>.fst.lower.get rfl

def rhs (T T' : Type) (Tₛ Tₛ' : String) : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    b1_t_i [type = "io"];
    b1_f_i [type = "io"];
    b2_t_i [type = "io"];
    b2_f_i [type = "io"];
    cond_i [type = "io"];
    b1_o [type = "io"];
    b2_o [type = "io"];

    joinT [typeImp = $(⟨_, join T T'⟩), type = $("join " ++ Tₛ ++ " " ++ Tₛ')];
    joinF [typeImp = $(⟨_, join T T'⟩), type = $("join " ++ Tₛ ++ " " ++ Tₛ')];
    mux [typeImp = $(⟨_, mux (T × T')⟩), type = $("mux (" ++ Tₛ ++ " × " ++ Tₛ' ++ ")")];
    split [typeImp = $(⟨_, split T T'⟩), type = $("split " ++ Tₛ ++ " " ++ Tₛ')];

    b1_t_i -> joinT [inp="inp0"];
    b2_t_i -> joinT [inp="inp1"];
    b1_f_i -> joinF [inp="inp0"];
    b2_f_i -> joinF [inp="inp1"];

    cond_i -> mux [inp="inp2"];

    joinT -> mux [out="out0", inp="inp0"];
    joinF -> mux [out="out0", inp="inp1"];
    mux -> split [out="out0", inp="inp0"];

    split -> b1_o [out="out0"];
    split -> b2_o [out="out1"];
  ]

def rhsLower T₁ T₂ := (rhs Unit Unit T₁ T₂).fst.lower.get rfl

theorem rhs_type_independent a b c d T₁ T₂ : (rhs a b T₁ T₂).fst = (rhs c d T₁ T₂).fst := by rfl

def rewrite (T₁ T₂ : String) : Rewrite String :=
  { abstractions := [],
    pattern := matcher T₁ T₂,
    input_expr := lhsLower T₁ T₂,
    output_expr := rhsLower T₁ T₂ }

end DataflowRewriter.CombineMux
