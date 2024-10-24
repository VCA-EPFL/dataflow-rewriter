/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.Module
import DataflowRewriter.Component
import DataflowRewriter.ExprHigh
import DataflowRewriter.Reduce

namespace DataflowRewriter

section BranchMerge


  -- TODO how to do polymorphic definition, here [out] is hardcoded and should be parametrized?
  -- TODO refer to other graph with proper namespacing, semantics either inline or do environment business
  -- TODO potentially woudl it be possible to automatically construct the environment if I use nonstrings.

  -- i.e.
  --   @[simp] def bagged  : ExprHigh String:=
    -- {[graph|
    --     enq [mod="io"];
    --     deq [mod="io"];

    --     m [mod=primitiveModule];
    -- ]}
  --  When I do that, it creates an environment when if primitiveModule is a
  --  graph, it first lowers it and interpret it, otherwise it just adds it
  --  directly. Unclear if it works


  @[simp] def bagged  : ExprHigh String:=
    [graph|
        enq  [mod="io"];
        enqT [mod="io"];
        deq  [mod="io"];

        m [mod="m"];
        bag [mod="bag"];
        joiner [mod="join"];
        -- Producing the tagged values
        m -> joiner[inp="inp0", out="out"];
        enqT -> joiner[inp="inp1", out="deq"];
        -- Push into the bag
        joiner -> bag [inp = "enq", out = "out"];
        -- Connecting with the exporting interface
        bag -> deq [inp ="deq", out="deq"];
        enq -> m[inp ="inp", out="enq"];
    ]

  def test  TagT T (m: Σ S, StringModule S) :=
   bagged.build_module [("m", m), ("bag", ⟨_,Module.bagS (T × TagT)⟩), ("join", ⟨_,(Module.join T TagT).stringify⟩)].toAssocList

example y : (fun S TagT T input output internals =>
  test TagT T ⟨S, ({ inputs := [(⟨ .top, "inp"⟩ , input)].toAssocList,
                     outputs := [(⟨ .top, "out"⟩ , output)].toAssocList,
                     internals := internals })⟩) = y := by
  dsimp only [test,drunfold,seval,Batteries.AssocList.toList,bagged,Function.uncurry,Module.mapIdent,List.toAssocList,List.foldl,Batteries.AssocList.find?,Option.pure_def,Option.bind_eq_bind,Option.bind_some,Module.renamePorts,Batteries.AssocList.mapKey,InternalPort.map,toString,Nat.repr,Nat.toDigits,Nat.toDigitsCore,Nat.digitChar,List.asString,Option.bind,Batteries.AssocList.mapVal,Batteries.AssocList.erase,Batteries.AssocList.eraseP,beq_self_eq_true,Option.getD,cond,beq_self_eq_true, beq_iff_eq, InternalPort.mk.injEq, String.reduceEq, and_false, imp_self]
  -- nearly there
  sorry

@[drunfold]
def tagged_ooo_h : ExprHigh String :=
[graph|
    enq [mod="io"];
    deq [mod="io"];

    tagger [mod="tag"];
    bagged [mod="bag"];
    join [mod="join"];

    -- Match tag and input
    -- Top-level inputs: The second input to join which is unbound
    tagger -> join [inp = "inp0", out = "out0"];
    enq -> join [out = "enq", inp = "inp1"];

    -- Feed the pair to the bag
    join -> bagged [inp = "enq", out = "out0"];

    -- Output of the bag complete inside the tagger
    bagged -> tagger [inp = "inp0", out = "deq"];

    -- Top-level outputs: Second output of the tagger, the untagged value which is unbound
    tagger -> deq [out = "out1", inp = "deq"];
  ]

end BranchMerge

end DataflowRewriter
