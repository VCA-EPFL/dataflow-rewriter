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

set_option Elab.async false

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

  theorem f_cast {f : Type _ → Type _} {a a'} (heq : a = a') : f a = f a' :=
    by subst a; rfl

  theorem rw_opaque_fst {f : Type _ → Type _} {a b a'} (heq : a = a') :
  Opaque (@Sigma.mk _ f a b).snd ↔ Opaque (@Sigma.mk _ f a' ((f_cast heq).mp b)).snd := by
    subst a; rfl

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
        dsimp [Module.product]
    )]
    dsimp [drcomponents]
    dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
    have := Module.foldl_acc_plist_2
        (acc := ⟨Unit,
          {
            inputs := AssocList.nil,
            outputs := AssocList.nil,
            init_state := fun x => True
          }
        ⟩)
      (l := fin_range n.topology.netsz)
      (f := λ acc1 _ => acc1 × EC.rmod.1)
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
    rw [this]
    clear this
    dsimp [Module.connect']
    rw [Module.foldl_acc_plist_expand]
    rw [rw_opaque_fst (by
      rw [Module.dep_foldl_1 (f := λ acc i => acc), List.foldl_fixed]
    )]
    simp only [drcompute]
    -- We still need to lower folds, but it is hard because we have cross
    -- dependency in the fold between internals to inputs and outputs
    -- Cannot apply the strong lemma here because he have a dependency between
    -- internal, output and inputs…
    -- We can maybe lower the fold for inputs, outputs and internals, and keep a
    -- weird fold for the internals…

    -- have := Module.foldl_acc_plist_2 (f := λ acc1 _ => acc1)
    --   (g_inputs := λ acc (i : n.topology.conn) =>
    --           AssocList.eraseAll
    --             { inst := InstIdent.internal (toString "Router " ++ toString i.snd.fst ++ toString ""),
    --               name := toString "in" ++ toString (↑i.snd.snd.2 + 1) ++ toString "" }
    --             acc.snd)
    --   (g_outputs := λ acc (i : n.topology.conn) =>
    --           AssocList.eraseAll
    --             { inst := InstIdent.internal (toString "Router " ++ toString i.fst ++ toString ""),
    --               name := toString "out" ++ toString (↑i.snd.snd.1 + 1) ++ toString "" }
    --             acc.snd)
    --   (g_internals := λ acc (i : n.topology.conn) =>
    --           Module.connect''
    --               (acc.snd.outputs.getIO
    --                   { inst := InstIdent.internal (toString "Router " ++ toString i.fst ++ toString ""),
    --                     name := toString "out" ++ toString (↑i.snd.snd.1 + 1) ++ toString "" }).snd
    --               (acc.snd.inputs.getIO
    --                   { inst := InstIdent.internal (toString "Router " ++ toString i.snd.fst ++ toString ""),
    --                     name := toString "in" ++ toString (↑i.snd.snd.2 + 1) ++ toString "" }).snd ::
    --             acc.snd.internals,
    -- rw [this]
    -- clear this

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
