/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Lean
import Qq

import DataflowRewriter.Reduce

open Lean Meta Elab Tactic

/--
Tactic to specialize all the hypotheses in the context that contain an binding
of that term in the first position.
-/
syntax (name := specializeAll) "specializeAll " term : tactic

@[tactic specializeAll] def specializeAllTactic : Tactic -- Syntax -> TacticM Unit
  | `(tactic| specializeAll $t:term) => withMainContext do
    let t ← elabTerm t none
    let termType ← inferType t
    let lctx ← getLCtx
    lctx.forM fun decl : LocalDecl => do
      -- First we check if the current hypothesis contains a binding of the same
      -- type as the input term in the first position.
      if (← forallTelescopeReducing decl.type fun vars _ => do
        if h : vars.size > 0 then
          isDefEq (← inferType vars[0]) termType
        else
          return false)
        -- We don't want to instantiate arrow types (only dependent types).
        && decl.type.arrow?.isNone
      then
        let e ← mkAppM' decl.toExpr #[t]
        -- We create a new assertion in the current goal and also infer the type
        -- of `e` again.  Instead we could generate the correct type as well.
        let mvarId ← (← getMainGoal).assert decl.userName (← inferType e).headBeta e
        let (_, mvarId) ← mvarId.intro1P
        let mvarId ← mvarId.tryClear decl.fvarId
        replaceMainGoal [mvarId]
      else
        return ()
  | _ => throwUnsupportedSyntax

elab "precompute " t:term : tactic => Tactic.withMainContext do
  let expr ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsUsingDefault
  let expr ← Lean.instantiateMVars expr
  let expr ←
    -- withTransparency .all <|
      reallyReduce (skipArgs := false) (skipTypes := false) expr
  (← Tactic.getMainGoal).assign expr

/--
Opaque definition used to lift any type into a `Prop`, so that it can be used as
the goal in `TacticM` mode.
-/
@[irreducible] def Opaque {A : Sort _} (_ : A) : Prop := False

open Qq in
/--
Run a tactic on an expression which must be a `Prop`.  The expression is set to
be the current goal, then the tactic is executed.  The modified goal is then
returned as the new expression.
-/
def evalTacticOnExprNoWrap (tac : Syntax) (e : Q(Prop)) : TacticM Q(Prop) := do
  let s ← saveState
  let l ← mkFreshExprMVar e
  setGoals [l.mvarId!]
  evalTactic tac
  let new_e ← getMainTarget
  restoreState s
  return new_e

open Qq in
/--
Run a tactic on an expression of any type.  This wraps the expression using
`Opaque`, which transforms it into a `Prop` so that it can be set to the current
goal.
-/
def evalTacticOnExpr (tac : Syntax) (e : Expr) : TacticM Expr := do
  let e' ← mkAppOptM ``Opaque #[(← inferType e), e]
  match ← evalTacticOnExprNoWrap tac e' with
  | ~q(Opaque $e) => return e
  | _ => throwError "Not in correct form"

open Qq in
elab "precomputeTac " t:term " by " tac:tacticSeq : tactic => Tactic.withMainContext do
  let expr ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsUsingDefault
  let expr ← Lean.instantiateMVars expr
  let exprType ← inferType expr
  let opaqueExpr ← mkAppOptM ``Opaque #[exprType, expr]
  let m ← mkFreshExprMVar opaqueExpr
  let (l :: s) ← evalTacticAt tac m.mvarId!
    | logError "No mvar returned"
  let r := (← l.getDecl).type.getArg!' 1
  (← getMainGoal).assign r

syntax (name := haveByLet) "have_hole " haveDecl : tactic
macro_rules
  | `(tactic| have_hole $id:ident $bs* : $type := $proof) =>
    `(tactic| (let h $bs* : $type := $proof; have $id:ident := h; clear h))
