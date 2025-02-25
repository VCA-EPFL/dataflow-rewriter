/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.Rewriter
import DataflowRewriter.ExprHighElaborator

namespace DataflowRewriter.SplitSinkLeft

open StringModule

variable (T T' : Type)
variable (S S' : String)

def matcher (g : ExprHigh String) : RewriteResult (List String × List String) := do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
       if s.isSome then return s
       unless "split".isPrefixOf typ do return none

       let (.some sink) := followOutput g inst "out1" | return none
       unless "sink".isPrefixOf sink.typ do return none

       let (.some t1) := typ.splitOn |>.get? 1 | return none
       let (.some t2) := typ.splitOn |>.get? 2 | return none
       let (.some t3) := sink.typ.splitOn |>.get? 1 | return none

       unless t1 = t3 do return none

       return some ([inst, sink.inst], [t1, t2])
    ) none | MonadExceptOf.throw RewriteError.done
  return list

def lhs : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i [type = "io"];
    o [type = "io"];

    split [typeImp = $(⟨_, split T T'⟩), type = $(s!"split {S} {S'}")];
    sink [typeImp = $(⟨_, sink T⟩), type = $(s!"sink {S}")];

    i -> split [to="in1"];
    split -> o [from="out2"];

    split -> sink [from="out1", to="in1"];
  ]

def lhs_extract := (lhs Unit Unit S S').fst.extract ["split", "sink"] |>.get rfl

theorem double_check_empty_snd : (lhs_extract S S').snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := (lhs_extract S S').fst.lower.get rfl

def rhs : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i [type = "io"];
    o [type = "io"];

    pure [typeImp = $(⟨_, @pure (T × T') _ Prod.snd⟩), type = $(s!"pure ({S}×{S'}) {S'}")];

    i -> pure [to="in1"];
    pure -> o [from="out1"];
  ]

def rhsLower := (rhs Unit Unit S S').fst.lower.get rfl

def rewrite : Rewrite String :=
  { abstractions := [],
    pattern := matcher,
    rewrite := λ | [S, S'] => .some ⟨lhsLower S S', rhsLower S S'⟩ | _ => failure
    name := "split-sink-left"
  }

end DataflowRewriter.SplitSinkLeft
