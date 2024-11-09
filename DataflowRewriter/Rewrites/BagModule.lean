/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.Rewriter
import DataflowRewriter.ExprHighElaborator

namespace DataflowRewriter.BranchMuxToMerge

opaque oracle : ExprHigh String → RewriteResult (List String)

/--
Instead of using dominators we can also use the fork and the condition circuit
to match the graph.
-/
def matcher (g : ExprHigh String) : RewriteResult (List String) := do
  return findType g "module"

def lhs' : ExprHigh String := [graph|
    i_in [type = "io"];
    o_out [type = "io"];

    module [type = "module"];

    i_in -> module [inp = "in"];
    module -> o_out [out = "out"];
  ]

#eval IO.print lhs'
-- #eval IO.print lhs'.invert
#eval IO.print lhs'

def lhs := lhs'.extract (matcher lhs' |>.toOption |>.get rfl) |>.get rfl

theorem double_check_empty_snd : lhs.snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := lhs.fst.lower.get rfl

def rhs : ExprHigh String := [graph|
    i_in [type = "io"];
    o_out [type = "io"];

    tagger [type = "TaggerCntrlAligner"];
    split [type = "TaggedSplit"];
    join [type = "TaggedJoin"];
    bag [type = "Bag"];
    module [type = "module"];

    i_in -> tagger [inp = "enq_untagged"];
    tagger -> split [out = "tagged", inp = "inp0"];

    split -> module [out = "out1", inp = "in"];
    split -> join [out = "out0", inp = "inp0"];
    module -> join [out = "out", inp = "inp1"];

    join -> bag [out = "out0", inp = "inp0"];
    bag -> tagger [out = "out0", inp = "complete_tagged"];

    tagger -> o_out [out = "deq_untagged"];
  ]

#eval IO.print rhs

def rhsLower := rhs.lower.get rfl

/--
This rewrite adds abstractions to the definition, which provide patterns to
extract parts of the graph.  The `type` given to each extracted node has to
match the `type` of the node in LHS and RHS graphs.
-/
def rewrite : Rewrite String :=
  { abstractions := [⟨oracle, "module"⟩],
    pattern := matcher,
    input_expr := lhsLower,
    output_expr := rhsLower }

end DataflowRewriter.BranchMuxToMerge
