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
      unless mux_nn.typ = "mux " ++ T && mux_nn.inputPort = "inp0" do return none
      unless mux_nn'.typ = "mux " ++ T' && mux_nn'.inputPort = "inp0" do return none
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

    mux1 -> b1_o [from="out0"];
    mux2 -> b2_o [from="out0"];

    cond_i -> condFork [to="inp0"];
    b1_t_i -> mux1 [to="inp1"];
    b1_f_i -> mux1 [to="inp2"];
    b2_t_i -> mux2 [to="inp1"];
    b2_f_i -> mux2 [to="inp2"];

    condFork -> mux1 [from="out0", to="inp0"];
    condFork -> mux2 [from="out1", to="inp0"];
  ]

-- #reduce lhs Unit Unit "H" "Y"

def lhs_extract T₁ T₂ := (lhs Unit Unit T₁ T₂).fst.extract ["mux1", "mux2", "condFork"] |>.get rfl

#eval IO.print (lhs_extract "T" "T'").fst

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

    b1_t_i -> joinT [to="inp0"];
    b2_t_i -> joinT [to="inp1"];
    b1_f_i -> joinF [to="inp0"];
    b2_f_i -> joinF [to="inp1"];

    cond_i -> mux [to="inp0"];

    joinT -> mux [from="out0", to="inp1"];
    joinF -> mux [from="out0", to="inp2"];
    mux -> split [from="out0", to="inp0"];

    split -> b1_o [from="out0"];
    split -> b2_o [from="out1"];
  ]

def rhsLower T₁ T₂ := (rhs Unit Unit T₁ T₂).fst.lower.get rfl

#eval IO.print ((rhs Unit Unit "T" "T'").fst)

theorem rhs_type_independent a b c d T₁ T₂ : (rhs a b T₁ T₂).fst = (rhs c d T₁ T₂).fst := by rfl

def rewrite (T₁ T₂ : String) : Rewrite String :=
  { abstractions := [],
    pattern := matcher T₁ T₂,
    input_expr := lhsLower T₁ T₂,
    output_expr := rhsLower T₁ T₂ }

end DataflowRewriter.CombineMux
