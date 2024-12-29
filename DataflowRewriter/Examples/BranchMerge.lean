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

attribute [drcompute] Batteries.AssocList.toList Function.uncurry Module.mapIdent List.toAssocList List.foldl Batteries.AssocList.find? Option.pure_def Option.bind_eq_bind Option.bind_some Module.renamePorts Batteries.AssocList.mapKey InternalPort.map toString Nat.repr Nat.toDigits Nat.toDigitsCore Nat.digitChar List.asString Option.bind Batteries.AssocList.mapVal Batteries.AssocList.eraseAll Batteries.AssocList.eraseP beq_self_eq_true Option.getD cond beq_self_eq_true  beq_iff_eq  InternalPort.mk.injEq  String.reduceEq  and_false  imp_self BEq.beq

attribute [drdecide] InternalPort.mk.injEq and_false decide_False decide_True and_true Batteries.AssocList.eraseAllP  InternalPort.mk.injEq
  and_false  decide_False  decide_True  reduceCtorEq  cond  List.map

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
        m -> joiner [out="out", inp="in2"];
        -- Push into the bag
        joiner -> bags [out = "out1", inp = "enq"];
        -- Connecting with the exporting interface
        bags -> deq [out="deq"];
        enq -> m [inp ="inp"];
        enqT -> joiner [inp="in1"];
    ]

#reduce bagged
#reduce bagged.lower

def test  TagT T S input output internals :=
   bagged.build_module [("m", ⟨S, ({ inputs := [(⟨ .top, "inp"⟩ , input)].toAssocList,
                                     outputs := [(⟨ .top, "out"⟩ , output)].toAssocList,
                                     internals := internals })⟩), ("bag", ⟨_,StringModule.bag (TagT × T)⟩), ("join", ⟨_,(NatModule.join TagT T).stringify⟩)].toAssocList

#check test

def test2 (TagT T S : Type) (input output : (T : Type) × (S → T → S → Prop))
  (internals : List (S → S → Prop)) : (T : Type) × Module String T := by
  precomputeTac test TagT T S input output internals by
    dsimp only [test,drunfold,seval,drcompute]
    simp only [seval,drdecide]
    conv in Module.connect'' _ _ => rw [Module.connect''_dep_rw]; rfl
    conv in _ :: Module.connect'' _ _ :: _ => arg 2; rw [Module.connect''_dep_rw]; rfl
    unfold Module.connect''
    dsimp

#print test2

-- TODO: Remove join here
@[drunfold]
def tagged_ooo_h : ExprHigh String :=
[graph|
    enq [mod="io"];
    deq [mod="io"];

    tagger [mod="tag"];
    bagged [mod="baggedModule"];

    -- Match tag and input
    -- Top-level inputs: The second input to join which is unbound
    tagger -> bagged [out = "out1", inp = "enqT"];
    enq -> bagged [inp = "enq"];

    -- Output of the bag complete inside the tagger
    bagged -> tagger [out = "deq", inp = "in1"];

    -- Top-level outputs: Second output of the tagger, the untagged value which is unbound
    tagger -> deq [out = "out2"];
  ]

def test3 TagT [h: DecidableEq TagT] T S input output internals :=
   tagged_ooo_h.build_module [("baggedModule", (test2 TagT T S input output internals)), ("tag", ⟨_,(NatModule.tag_complete_spec TagT T).stringify⟩),("bag", ⟨_,StringModule.bagS (T × TagT)⟩), ("join", ⟨_,(NatModule.join T TagT).stringify⟩)].toAssocList

#reallyReduce test3

def test4 (TagT T S : Type) [h:DecidableEq TagT] (input output : (T : Type) × (S → T → S → Prop))
  (internals : List (S → S → Prop))
  : (T : Type) × Module String T := by precomputeTac @test3 TagT h T S input output internals by
    dsimp only [test3,test2,bagged,drunfold,seval,drcompute]
    simp only [seval,drdecide]
    conv in Module.connect'' _ _ => rw [Module.connect''_dep_rw]; rfl
    conv in _ :: Module.connect'' _ _ :: _ => arg 2; rw [Module.connect''_dep_rw]; rfl
    unfold Module.connect'' Module.liftR' Module.liftL'
    dsimp

end BranchMerge

end DataflowRewriter
