/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.Rewriter
import DataflowRewriter.ExprHighElaborator

/-
This file transforms every node in a datapath into a pure module with a combination of splits and joins.  This format
can then be optimised externally by egg, and the proof can be reconstructed on the graph.

The file contains all rewrites for this purpose, as they are all relatively simple.
-/

namespace DataflowRewriter.PureRewrites

open StringModule

namespace Constant

def matcher (g : ExprHigh String) : RewriteResult (List String × List String) := sorry

variable (n : Nat)

def lhs : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i [type = "io"];
    o [type = "io"];

    const [typeImp = $(⟨_, constant n⟩), type = $(s!"constant {n}")];

    i -> const [to="in1"];
    const -> o [from="out1"];
  ]

def lhs_extract := (lhs n).fst.extract ["const"] |>.get rfl

theorem double_check_empty_snd : (lhs_extract n).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := lhs_extract n |>.fst.lower.get rfl

def rhs : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i [type = "io"];
    o [type = "io"];

    const [typeImp = $(⟨_, pure (S := Unit) λ _ => n⟩), type = $(s!"pure λ_=>{n}")];

    i -> const [to="in1"];
    const -> o [from="out1"];
  ]

def rhsLower := (rhs n).fst.lower.get rfl

def rewrite : Rewrite String :=
  { abstractions := [],
    pattern := matcher,
    rewrite := λ l => do
      let n' ← l.get? 0
      -- SOMEDAY: Replace this by a proper Nat parser
      let exp ← Lean.Json.Parser.num.run n' |>.toOption
      let parsed ← exp.mantissa.toNat'
      return ⟨ lhsLower parsed, rhsLower parsed ⟩
    name := .some "pure-constant"
  }

end Constant

namespace Operator1

def matcher (g : ExprHigh String) : RewriteResult (List String × List String) := sorry

variable (T : Type)
variable [Inhabited T]
variable (Tₛ : String)
variable (Op : String)

def lhs : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i [type = "io"];
    o [type = "io"];

    op [typeImp = $(⟨_, operator1 T Op⟩), type = $(s!"operator1 {Tₛ} {Op}")];

    i -> op [to="in1"];
    op -> o [from="out1"];
  ]

def lhs_extract := (lhs Unit Tₛ Op).fst.extract ["op"] |>.get rfl

theorem double_check_empty_snd : (lhs_extract Tₛ Op).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := lhs_extract Tₛ Op |>.fst.lower.get rfl

def rhs : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i [type = "io"];
    o [type = "io"];

    op [typeImp = $(⟨_, StringModule.pure λ x => @NatModule.op1_function T _ Op x⟩),
        type = $(s!"pure λ x => @op1_function {Tₛ} _ {Op} x")];

    i -> op [to="in1"];
    op -> o [from="out1"];
  ]

def rhsLower := (rhs Unit Tₛ Op).fst.lower.get rfl

def rewrite : Rewrite String :=
  { abstractions := [],
    pattern := matcher,
    rewrite :=
      λ | [Ts, Ops] => .some ⟨ lhsLower Ts Ops, rhsLower Ts Ops ⟩
        | _ => .none
    name := .some "pure-operator1"
  }

end Operator1

namespace Operator2

def matcher (g : ExprHigh String) : RewriteResult (List String × List String) := sorry

variable (T : Type)
variable [Inhabited T]
variable (Tₛ : String)
variable (Op : String)

def lhs : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i1 [type = "io"];
    i2 [type = "io"];
    o [type = "io"];

    op [typeImp = $(⟨_, operator2 T Op⟩), type = $(s!"operator2 {Tₛ} {Op}")];

    i1 -> op [to="in1"];
    i2 -> op [to="in2"];
    op -> o [from="out1"];
  ]

def lhs_extract := (lhs Unit Tₛ Op).fst.extract ["op"] |>.get rfl

theorem double_check_empty_snd : (lhs_extract Tₛ Op).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := lhs_extract Tₛ Op |>.fst.lower.get rfl

def rhs : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i1 [type = "io"];
    i2 [type = "io"];
    o [type = "io"];

    join [typeImp = $(⟨_, join T T⟩), type = $(s!"join {Tₛ} {Tₛ}")];
    op [typeImp = $(⟨_, StringModule.pure λ x => @NatModule.op2_function T _ Op x.1 x.2⟩),
        type = $(s!"pure λ x => @op2_function T _ Op x.1 x.2")];

    i1 -> join [to="in1"];
    i2 -> join [to="in2"];
    join -> op [from="out1", to="in1"];
    op -> o [from="out1"];
  ]

def rhsLower := (rhs Unit Tₛ Op).fst.lower.get rfl

def rewrite : Rewrite String :=
  { abstractions := [],
    pattern := matcher,
    rewrite :=
      λ | [Ts, Ops] => .some ⟨ lhsLower Ts Ops, rhsLower Ts Ops ⟩
        | _ => .none
    name := .some "pure-operator2"
  }

end Operator2

namespace Operator3

def matcher (g : ExprHigh String) : RewriteResult (List String × List String) := sorry

variable (T : Type)
variable [Inhabited T]
variable (Tₛ : String)
variable (Op : String)

def lhs : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i1 [type = "io"];
    i2 [type = "io"];
    i3 [type = "io"];
    o [type = "io"];

    op [typeImp = $(⟨_, operator3 T Op⟩), type = $(s!"operator3 {Tₛ} {Op}")];

    i1 -> op [to="in1"];
    i2 -> op [to="in2"];
    i3 -> op [to="in3"];
    op -> o [from="out1"];
  ]

def lhs_extract := (lhs Unit Tₛ Op).fst.extract ["op"] |>.get rfl

theorem double_check_empty_snd : (lhs_extract Tₛ Op).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := lhs_extract Tₛ Op |>.fst.lower.get rfl

def rhs : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i1 [type = "io"];
    i2 [type = "io"];
    i3 [type = "io"];
    o [type = "io"];

    join1 [typeImp = $(⟨_, join T T⟩), type = $(s!"join {Tₛ} {Tₛ}")];
    join2 [typeImp = $(⟨_, join T (T × T)⟩), type = $(s!"join {Tₛ} ({Tₛ}×{Tₛ})")];
    op [typeImp = $(⟨_, StringModule.pure λ (x : T × T × T) => @NatModule.op3_function T _ Op x.1 x.2.1 x.2.2⟩),
        type = $(s!"pure λ x => @op3_function T _ Op x.1 x.2.1 x.2.2")];

    i1 -> join2 [to="in1"];
    i2 -> join1 [to="in1"];
    i3 -> join1 [to="in2"];

    join1 -> join2 [from="out1",to="in2"];
    join2 -> op [from="out1", to="in1"];

    op -> o [from="out1"];
  ]

def rhsLower := (rhs Unit Tₛ Op).fst.lower.get rfl

def rewrite : Rewrite String :=
  { abstractions := [],
    pattern := matcher,
    rewrite :=
      λ | [Ts, Ops] => .some ⟨ lhsLower Ts Ops, rhsLower Ts Ops ⟩
        | _ => .none
    name := .some "pure-operator3"
  }

end Operator3

namespace Fork

def matcher (g : ExprHigh String) : RewriteResult (List String × List String) := sorry

variable (T : Type)
variable [Inhabited T]
variable (Tₛ : String)

def lhs : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i [type = "io"];
    o1 [type = "io"];
    o2 [type = "io"];

    fork [typeImp = $(⟨_, fork T 2⟩), type = $(s!"fork {Tₛ} 2")];

    i -> fork [to="in1"];
    fork -> o1 [from="out1"];
    fork -> o2 [from="out2"];
  ]

def lhs_extract := (lhs Unit Tₛ).fst.extract ["fork"] |>.get rfl

theorem double_check_empty_snd : (lhs_extract Tₛ).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := lhs_extract Tₛ |>.fst.lower.get rfl

def rhs : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i [type = "io"];
    o1 [type = "io"];
    o2 [type = "io"];

    op [typeImp = $(⟨_, StringModule.pure λ (x : T) => (x, x)⟩),
        type = $(s!"pure λx=>(x,x)")];
    split [typeImp = $(⟨_, split T T⟩), type = $(s!"split {Tₛ} {Tₛ}")];

    i -> op [to="in1"];
    op -> split [from="out1",to="in1"];
    split -> o1 [from="out1"];
    split -> o2 [from="out2"];
  ]

def rhsLower := (rhs Unit Tₛ).fst.lower.get rfl

def rewrite : Rewrite String :=
  { abstractions := [],
    pattern := matcher,
    rewrite :=
      λ | [Ts] => .some ⟨ lhsLower Ts, rhsLower Ts ⟩
        | _ => .none
    name := .some "pure-operator3"
  }

end Fork

end DataflowRewriter.PureRewrites
