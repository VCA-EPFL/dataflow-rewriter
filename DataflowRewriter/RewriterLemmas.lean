/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.ExprHighLemmas
import DataflowRewriter.Rewriter
import DataflowRewriter.Environment

open Batteries (AssocList)

namespace DataflowRewriter

structure CorrectRewrite where
  rewrite : Rewrite String
  env : List String → Option Env
  consistent : ∀ l env', env l = .some env' → env'.subsetOf ε_global
  defined : ∀ l, (rewrite.rewrite l).isSome → (env l).isSome
  wf : ∀ l env' defrw, env l = .some env' → rewrite.rewrite l = .some defrw → defrw.input_expr.wf env' ∧ defrw.output_expr.wf env'
  refines :
    ∀ l defrw env',
      env l = .some env' →
      rewrite.rewrite l = .some defrw →
      [e| defrw.output_expr, env' ] ⊑ ([e| defrw.input_expr, env' ])

theorem EStateM.bind_eq_ok {ε σ α β} {x : EStateM ε σ α} {f : α → EStateM ε σ β} {s v s'} :
  x.bind f s = .ok v s' →
  ∃ (x_int : α) (s_int : σ),
    x s = .ok x_int s_int ∧ f x_int s_int = .ok v s' := by
  unfold EStateM.bind; split <;> tauto

theorem ofOption_eq_ok {ε σ α} {e : ε} {o : Option α} {o' : α} {s s' : σ} :
  ofOption e o s = EStateM.Result.ok o' s' →
  o = o' ∧ s = s' := by
  unfold ofOption
  split <;> (intros h; cases h)
  constructor <;> rfl

theorem liftError_eq_ok {σ α} {o : Except String α} {o' : α} {s s' : σ} :
  liftError o s = EStateM.Result.ok o' s' →
  o = .ok o' ∧ s = s' := by
  unfold liftError; split <;> (intros h; cases h)
  constructor <;> rfl

theorem guard_eq_ok {ε σ} {e : ε} {b : Bool} {o' : Unit} {s s' : σ} :
  EStateM.guard e b s = EStateM.Result.ok o' s' →
  b = true ∧ s = s' := by
  unfold EStateM.guard; split <;> (intros h; cases h)
  subst b; constructor <;> rfl

theorem EStateM.map_eq_ok {ε σ α β} {f : α → β} {o : EStateM ε σ α} {o' : β} {s s' : σ} :
  EStateM.map f o s = .ok o' s' →
  ∃ o'' s'', o s = .ok o'' s'' ∧ s' = s'' ∧ o' = f o'' := by
  unfold EStateM.map; split <;> (intros h; cases h)
  constructor; constructor; and_intros <;> solve | assumption | rfl

-- theorem addRewriteInfo_eq_ok {r : RewriteInfo} {s s' : List RewriteInfo} {o' : Unit} :
--   addRewriteInfo r s = .ok o' s' → s' = r :: s := by
--   unfold addRewriteInfo; simp
--   sorry

theorem refines_higherSS {e : ExprLow String} {e' : ExprHigh String} :
  e.higherSS = .some e' →
  [Ge| e', ε_global] ⊑ ([e| e, ε_global]) := by sorry

theorem wf_mapping_all {e : ExprLow String}:
  e.wf_mapping ε_global := by sorry

theorem wf_expr_all {e : ExprLow String}:
  e.wf ε_global := by sorry

theorem Rewrite_run'_correct {g g' : ExprHigh String} {s _st _st'} {rw : CorrectRewrite} :
  Rewrite.run' s g rw.rewrite _st = .ok g' _st' →
  ([Ge| g', ε_global ]) ⊑ ([Ge| g, ε_global ]) := by
  unfold Rewrite.run'; simp; intro hrewrite
  dsimp [Bind.bind, Monad.toBind, EStateM.instMonad] at *
  repeat
    rename (EStateM.bind _ _ _ = .ok _ _) => hrewrite
    replace hrewrite := EStateM.bind_eq_ok hrewrite
    let ⟨_, _, _, hrewrite'⟩ := hrewrite
    clear hrewrite; have hrewrite := hrewrite'; clear hrewrite'
  repeat
    try have hofOption' := hofOption; clear hofOption
    rename (ofOption _ _ _ = .ok _ _) => hofOption
    replace hofOption := ofOption_eq_ok hofOption
    cases hofOption
  repeat
    try have hofOption' := hofOption; clear hofOption
    rename (liftError _ _ = .ok _ _) => hofOption
    replace hofOption := liftError_eq_ok hofOption
    cases hofOption
  repeat
    try have hofOption' := hofOption; clear hofOption
    rename (EStateM.guard _ _ _ = .ok _ _) => hofOption
    replace hofOption := guard_eq_ok hofOption
    cases hofOption
  repeat
    try have hofOption' := hofOption; clear hofOption
    rename (EStateM.map _ _ _ = .ok _ _) => hofOption
    replace hofOption := EStateM.map_eq_ok hofOption
    let ⟨_, _, _, _, _⟩ := hofOption; clear hofOption
  subst_vars
  repeat cases ‹Unit›
  rename List RewriteInfo => rewrite_info
  rename g.extract _ = _ => Hextract
  rename ExprHigh.lower _ = _ => Hlower
  rename rw.rewrite.rewrite _ = _ => Hrewrite
  rename ExprLow.weak_beq _ _ = _ => Hweakbeq
  rename rw.rewrite.pattern _ _ = _ => Hpattern
  rename PortMapping String × PortMapping String => ioPortMap
  rename ExprLow String => lowered
  clear ‹portmappingToNameRename' _ _ _ = _›
  clear ‹addRewriteInfo _ _ = _›
  rename ExprHigh String × ExprHigh String => extractedGraphs
  rename List String × List String => pattern
  rename DefiniteRewrite String => defrw
  rename ExprHigh String => outGraph
  clear ‹AssocList String (Option String)›
  rename ExprLow.higherSS _ = _ => Hhighering
  have := rw.defined _ (by rw [Hrewrite]; apply Option.isSome_some)
  rw [Option.isSome_iff_exists] at this; obtain ⟨l, r⟩ := this
  apply Module.refines_transitive
  apply refines_higherSS; assumption
  apply Module.refines_transitive
  apply ExprLow.refines_renamePorts_2
  apply wf_mapping_all
  rw [ExprLow.ensureIOUnmodified_correct] <;> try assumption
  rw [ExprLow.force_replace_eq_replace]
  apply Module.refines_transitive
  apply ExprLow.replacement
  apply wf_expr_all; apply wf_expr_all; apply wf_expr_all
  apply Module.refines_transitive
  apply ExprLow.refines_renamePorts_2
  apply wf_mapping_all
  apply Module.refines_transitive
  apply Module.refines_renamePorts
  apply ExprLow.refines_subset
  apply rw.consistent; assumption
  apply (rw.wf _ _ _ ‹_› ‹_›).2
  apply (rw.wf _ _ _ ‹_› ‹_›).1
  solve_by_elim [rw.refines]
  apply Module.refines_transitive
  apply ExprLow.refines_renamePorts_1
  apply wf_mapping_all
  apply ExprLow.refines_comm_connections2'
  apply wf_expr_all
  apply Module.refines_transitive
  apply ExprLow.refines_comm_connections'
  apply wf_expr_all
  apply Module.refines_transitive
  apply ExprLow.refines_comm_bases
  apply wf_expr_all
  unfold ExprHigh.build_module_expr ExprHigh.build_module ExprHigh.build_module'
  rw [‹g.lower = _›]
  dsimp
  apply Module.refines_reflexive

structure Pair (S T : Type) : Type where
  leftright : S × T

def denoteType' (str : String) (n : Nat) : Option (Type × String) :=
  match n with
  | n+1 =>
    let t := str.trim
    if t.front = '×' then denoteType' (t.drop 1) n
    else if "Nat".isPrefixOf t then pure (Nat, t.drop 3)
    else if "Bool".isPrefixOf t then pure (Bool, t.drop 4)
    else if "Unit".isPrefixOf t then pure (Unit, t.drop 4)
    else if t.front = '(' then do
      let (typ, c) ← denoteType' (t.drop 1) n
      let (typ', c') ← denoteType' c n
      return (typ × typ', c'.trim.drop 1)
    else failure
  | _ => .none

def denoteType (str : String) : Option (Type × String) :=
  denoteType' str str.length

example : ∀ y, y = denoteType " (Unit × Unit)" := by
  intro y
  simp +ground

-- open Lean Elab Term Meta Core in
-- #eval show IO Expr from TermElabM.toIO (do elabTerm (← `(StringModule.queue Nat)) .none) {fileName := "<rewriter environment>", fileMap := default} {}

  -- unfold EStateM.bind ofOption at *
  -- repeat (dsimp -failIfUnchanged at *; split at hrewrite <;> try injection hrewrite)
  -- set_option pp.explicit true in trace_state


theorem Rewrite_abstraction_correct {g g' : ExprHigh String} {s a c} :
  Abstraction.run s g a = .ok (g', c) →
  ([Ge| g', ε ]) ⊑ ([Ge| g, ε ]) := by sorry

theorem Rewrite_concretisation_correct {g g' : ExprHigh String} {s c} :
  Concretisation.run s g c = .ok g' →
  ([Ge| g', ε ]) ⊑ ([Ge| g, ε ]) := by sorry

theorem Rewrite_run_correct {g g' : ExprHigh String} {s rw} :
  Rewrite.run s g rw = .ok g' →
  ([Ge| g', ε ]) ⊑ ([Ge| g, ε ]) := by sorry

theorem rewrite_loop_correct {g g' : ExprHigh String} {s rws n} :
  rewrite_loop s g rws n = .ok g' →
  ([Ge| g', ε ]) ⊑ ([Ge| g, ε ]) := by sorry

end DataflowRewriter
