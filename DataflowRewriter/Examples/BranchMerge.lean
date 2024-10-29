/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.Module
import DataflowRewriter.Component
import DataflowRewriter.ExprHighLemmas
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
        bags [mod="bag"];
        joiner [mod="join"];
        -- Producing the tagged values
        m -> joiner [out="out", inp="inp0"];
        -- Push into the bag
        joiner -> bags [out = "out0", inp = "enq"];
        -- Connecting with the exporting interface
        bags -> deq [out="deq"];
        enq -> m [inp ="inp"];
        enqT -> joiner [inp="inp1"];
    ]

#reduce bagged
#reduce bagged.lower

def test  TagT T S input output internals :=
   bagged.build_module [("m", ⟨S, ({ inputs := [(⟨ .top, "inp"⟩ , input)].toAssocList,
                                     outputs := [(⟨ .top, "out"⟩ , output)].toAssocList,
                                     internals := internals })⟩), ("bag", ⟨_,StringModule.bagS (T × TagT)⟩), ("join", ⟨_,(NatModule.join T TagT).stringify⟩)].toAssocList

#check test

def test2 (TagT T S : Type) (input output : (T : Type) × (S → T → S → Prop))
  (internals : List (S → S → Prop)) : (T : Type) × Module String T := by
  precomputeTac test TagT T S input output internals by
    unfold test
    dsimp only [test,drunfold,seval,Batteries.AssocList.toList,bagged,Function.uncurry,Module.mapIdent,List.toAssocList,List.foldl,Batteries.AssocList.find?,Option.pure_def,Option.bind_eq_bind,Option.bind_some,Module.renamePorts,Batteries.AssocList.mapKey,InternalPort.map,toString,Nat.repr,Nat.toDigits,Nat.toDigitsCore,Nat.digitChar,List.asString,Option.bind,Batteries.AssocList.mapVal,Batteries.AssocList.eraseAll,Batteries.AssocList.eraseAllP,beq_self_eq_true,Option.getD,cond,beq_self_eq_true, beq_iff_eq, InternalPort.mk.injEq, String.reduceEq, and_false, imp_self,BEq.beq]
    simp (config := {decide := true,maxSteps := 10000000}) only [seval,InternalPort.mk.injEq, and_false, decide_False, decide_True, and_true]
    conv in Module.connect'' _ _ => rw [Module.connect''_dep_rw]; rfl
    conv in _ :: Module.connect'' _ _ :: _ => arg 2; rw [Module.connect''_dep_rw]; rfl
    unfold Module.connect''

#print test2

-- TODO: Remove join here
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

def test3  TagT [h: DecidableEq TagT] T (m: Σ S, StringModule S) :=
   tagged_ooo_h.build_module [("m", m), ("tag", ⟨_,(NatModule.tag_complete_spec TagT T).stringify⟩),("bag", ⟨_,StringModule.bagS (T × TagT)⟩), ("join", ⟨_,(NatModule.join T TagT).stringify⟩)].toAssocList


def test4  TagT [h: DecidableEq TagT] (T : Type) (m: Σ S, StringModule S)
  : (T : Type) × Module String T := by precomputeTac test3 TagT T m by
    dsimp only [test3,drunfold,seval,Batteries.AssocList.toList,bagged,Function.uncurry,Module.mapIdent,List.toAssocList,List.foldl,Batteries.AssocList.find?,Option.pure_def,Option.bind_eq_bind,Option.bind_some,Module.renamePorts,Batteries.AssocList.mapKey,InternalPort.map,toString,Nat.repr,Nat.toDigits,Nat.toDigitsCore,Nat.digitChar,List.asString,Option.bind,Batteries.AssocList.mapVal,Batteries.AssocList.eraseAll,Batteries.AssocList.eraseP,beq_self_eq_true,Option.getD,cond,beq_self_eq_true, beq_iff_eq, InternalPort.mk.injEq, String.reduceEq, and_false, imp_self,BEq.beq]
    simp (config := {decide := true,maxSteps := 10000000,ground := true,autoUnfold := true}) only [seval,InternalPort.mk.injEq, and_false, decide_False, decide_True, and_true]
    set_option pp.piBinderTypes  true in set_option pp.letVarTypes true in set_option pp.structureInstances false in set_option pp.fieldNotation false in set_option pp.funBinderTypes true in set_option pp.explicit true in set_option pp.deepTerms true in set_option pp.maxSteps 1000000000 in trace_state
    conv in Module.connect'' _ _ => rw [Module.connect''_dep_rw]; rfl
    conv in _ :: Module.connect'' _ _ :: _ => arg 2; rw [Module.connect''_dep_rw]; rfl
    conv in _ :: Module.connect'' _ _ :: _ => arg 2; arg 2; rw [Module.connect''_dep_rw]; rfl
    unfold Module.connect''
    dsimp

end BranchMerge

end DataflowRewriter
