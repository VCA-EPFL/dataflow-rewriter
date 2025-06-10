/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import DataflowRewriter.Module
import DataflowRewriter.ModuleLemmas
import DataflowRewriter.ModuleReduction
import DataflowRewriter.ExprLow
import DataflowRewriter.ExprLowLemmas
import DataflowRewriter.Component
import DataflowRewriter.Examples.Noc.Utils
import DataflowRewriter.Examples.Noc.Lang
import DataflowRewriter.Examples.Noc.Spec
import DataflowRewriter.Examples.Noc.BuildExpr

open Batteries (AssocList)

namespace DataflowRewriter.Noc

  variable {Data : Type} [BEq Data] [LawfulBEq Data]

  def Noc.env_rmod_ok (n : Noc Data) (rmod : TModule String) : Prop :=
    ∀ rid : n.RouterID, rmod.2 ⊑ (n.spec_router rid)

  @[drenv]
  def Noc.env_rmod_in (n : Noc Data) (ε : Env) (rmod : TModule String) : Prop :=
    ∀ rid : n.RouterID, AssocList.find? (router_name n rid) ε = .some rmod

  @[drenv]
  def Noc.env_empty (n : Noc Data) (ε : Env) : Prop :=
    AssocList.find? "empty" ε = .some ⟨Unit, StringModule.empty⟩

  class EnvCorrect (n : Noc Data) (ε : Env) where
    rmod        : TModule String
    rmod_ok     : n.env_rmod_ok rmod
    rmod_in_ε   : n.env_rmod_in ε rmod
    empty_in_ε  : n.env_empty ε

  variable (n : Noc Data) (ε : Env) [EC : EnvCorrect n ε]

  abbrev mod := NatModule.stringify n.build_module

  theorem tmodule_renamePorts_1 {Ident} [DecidableEq Ident] (a : TModule Ident) (p : PortMapping Ident) :
   (⟨a.1, a.2.renamePorts p⟩ : TModule Ident).1 = a.1 := by rfl

  theorem tmodule_renamePorts_2 {Ident} [DecidableEq Ident] (a : TModule Ident) (p : PortMapping Ident) :
   (⟨a.1, a.2.renamePorts p⟩ : TModule Ident).2 = a.2.renamePorts p := by rfl

  def_module expT : Type := [T| n.build_expr, ε] reduction_by
    dsimp [drunfold_defs, drcomponents]
    dsimp [ExprLow.build_module_type]
    rw [ExprLow.build_module_connect_foldl]
    rw [ExprLow.build_module_product_foldl]
    dsimp [ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module']
    rw [EC.empty_in_ε]
    conv =>
      pattern List.foldl _ _
      arg 2
      arg 1
      intro acc i
      rw [←router_name, EC.rmod_in_ε i]
      dsimp
    rw [Module.dep_foldl_1 (f := λ acc i => acc)]
    rw [Module.dep_foldl_1 (f := λ acc i => acc × EC.rmod.1)]
    simp only [drenv, drcompute, List.foldl_fixed]

  def expand_init {Ident} [DecidableEq Ident] (acc : TModule Ident) :
      acc.snd.init_state = (⟨acc.fst, acc.snd.init_state⟩ : Σ S, Module.acc_init S).snd := by rfl

  def expand_inputs {Ident} [DecidableEq Ident] (acc : TModule Ident) :
      acc.snd.inputs = (⟨acc.fst, acc.snd.inputs⟩ : Σ S, Module.acc_io S).snd := by rfl

  def expand_outputs {Ident} [DecidableEq Ident] (acc : TModule Ident) :
      acc.snd.outputs = (⟨acc.fst, acc.snd.outputs⟩ : Σ S, Module.acc_io S).snd := by rfl

  def expand_internals {Ident} [DecidableEq Ident] (acc : TModule Ident) :
      acc.snd.internals = (⟨acc.fst, acc.snd.internals⟩ : Σ S, Module.acc_int S).snd := by rfl

  def expand_t {Ident α} [DecidableEq Ident] (acc : TModule Ident) (i : α) :
    (acc.fst × (EnvCorrect.rmod n ε).fst) =
    (λ acc1 _ => acc1 × EC.rmod.1) acc.fst i := by rfl

  def_module expM : Module String (expT n ε) := [e| n.build_expr, ε] reduction_by
    dsimp [drunfold_defs, reduceAssocListfind?, reduceListPartition]
    dsimp [ExprLow.build_module_expr, ExprLow.build_module_type]
    rw [ExprLow.build_module_connect_foldl]
    rw [ExprLow.build_module_product_foldl]
    dsimp [ExprLow.build_module, ExprLow.build_module']
    rw [EC.empty_in_ε]; dsimp
    rw [rw_opaque (by
      conv =>
        pattern List.foldl _ _
        arg 2
        arg 1
        intro acc i
        rw [←router_name, EC.rmod_in_ε i]
        -- dsimp [Module.product]
    )]
    dsimp [drcomponents]
    dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
    rw [rw_opaque (by
      conv =>
        pattern List.foldl _ _
        arg 2
        arg 1
        intro acc i
        rw [expand_internals, expand_init, expand_outputs, expand_inputs]
        -- rw [expand_t n ε acc i]
    )]
    -- rw [rw_opaque (by rw [Module.foldl_acc_plist_2])]
    rw [rw_opaque (by
      conv =>
        pattern List.foldl _ _
        arg 2
    )]
    -- Not working :(
    -- But almost there...
    -- I think the automatic rewrite may just be having issue with dependent
    -- types but that it is correct
    have Htmp := @Module.foldl_acc_plist_2 String n.RouterID
        ⟨Unit,
          {
            inputs := AssocList.nil,
            outputs := AssocList.nil,
            init_state := fun x => True
          }
        ⟩
      (fin_range n.topology.netsz)
      (λ acc1 _ => acc1 × EC.rmod.1)
      (g_inputs := λ acc i =>
        AssocList.mapVal (λ x => Module.liftL) acc.snd ++
          AssocList.mapVal (λ x => Module.liftR)
            (AssocList.mapKey
              (AssocList.cons
                  { inst := InstIdent.top,
                    name := toString "Router " ++ toString i ++ toString " in" ++ "0" ++ toString "" }
                  { inst := InstIdent.top, name := toString "in" ++ toString (↑i + 1) ++ toString "" }
                  ((n.topology.neigh_inp i).mapFinIdx fun dir x h =>
                      ({ inst := InstIdent.top,
                          name :=
                            toString "Router " ++ toString i ++ toString " in" ++ toString (dir + 1) ++
                              toString "" },
                        { inst := InstIdent.internal (toString "Router " ++ toString i ++ toString ""),
                          name :=
                            toString "in" ++ toString (dir + 1 + 1) ++
                              toString "" })).toAssocList).bijectivePortRenaming
              (EnvCorrect.rmod n ε).snd.inputs)
      )
      (g_outputs := λ acc i =>
        AssocList.mapVal (fun x => Module.liftL) acc.snd ++
          AssocList.mapVal (fun x => Module.liftR)
            (AssocList.mapKey
              (AssocList.cons
                  { inst := InstIdent.top,
                    name := toString "Router " ++ toString i ++ toString " out" ++ "0" ++ toString "" }
                  { inst := InstIdent.top, name := toString "out" ++ toString (↑i + 1) ++ toString "" }
                  ((n.topology.neigh_out i).mapFinIdx fun dir x h =>
                      ({ inst := InstIdent.top,
                          name :=
                            toString "Router " ++ toString i ++ toString " out" ++ toString (dir + 1) ++
                              toString "" },
                        { inst := InstIdent.internal (toString "Router " ++ toString i ++ toString ""),
                          name :=
                            toString "out" ++ toString (dir + 1 + 1) ++
                              toString "" })).toAssocList).bijectivePortRenaming
              (EnvCorrect.rmod n ε).snd.outputs)
      )
      (g_internals := λ acc i =>
        List.map Module.liftL' acc.snd ++ List.map Module.liftR' (EnvCorrect.rmod n ε).snd.internals
      )
      (g_init_state := λ acc i =>
        fun x => acc.snd x.1 ∧ (EnvCorrect.rmod n ε).snd.init_state x.2
      )
    rw [Htmp]

  instance : MatchInterface (mod n) (expM n ε) := by
    apply MatchInterface_simpler
    <;> intro _
    <;> dsimp [drunfold_defs, drcomponents]
    <;> sorry

  def φ (I : n.State) (S : expT n ε) : Prop :=
    sorry

  theorem refines_initial : Module.refines_initial (mod n) (expM n ε) (φ n ε) := by
    sorry

  theorem refines_φ : (mod n) ⊑_{φ n ε} (expM n ε) := by
    sorry

  theorem ϕ_indistinguishable :
    ∀ i s, (φ n ε) i s → Module.indistinguishable (mod n) (expM n ε) i s := by
      sorry

  theorem correct : (mod n) ⊑ (expM n ε) := by
    apply (
      Module.refines_φ_refines
        (ϕ_indistinguishable n ε)
        (refines_initial n ε)
        (refines_φ n ε)
    )

end DataflowRewriter.Noc
