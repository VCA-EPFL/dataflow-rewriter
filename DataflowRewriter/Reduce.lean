import Lean
import Mathlib

open Lean Expr Meta

partial def reallyReduce (e : Expr) (explicitOnly skipTypes skipProofs skipArgs := true) : MetaM Expr :=
  let rec visit (e : Expr) : MonadCacheT Expr Expr MetaM Expr :=
    checkCache e fun _ => Core.withIncRecDepth do
      if (← (pure skipTypes <&&> isType e)) then
        return e
      else if (← (pure skipProofs <&&> isProof e)) then
        return e
      else
        let e ← whnf e
        match e with
        | Expr.app .. =>
          let f     ← visit e.getAppFn
          let nargs := e.getAppNumArgs
          let finfo ← getFunInfoNArgs f nargs
          let mut args  := e.getAppArgs
          for i in [:args.size] do
            if i < finfo.paramInfo.size then
              let info := finfo.paramInfo[i]!
              if !explicitOnly || info.isExplicit then
                args ← args.modifyM i visit
            else
              args ← args.modifyM i visit
          if f.isConstOf ``Nat.succ && args.size == 1 && args[0]!.isRawNatLit then
            return mkRawNatLit (args[0]!.rawNatLit?.get! + 1)
          else
            return mkAppN f args
        | Expr.lam ..        => lambdaTelescope e fun xs b => do 
          if skipArgs then mkLambdaFVars xs (← visit b)
          else
            let ctx ← getLCtx
            let ctx' ← xs.foldlM (fun ctx' e => do
              let e' ← visit (ctx'.getFVar! e).type
              return ctx'.modifyLocalDecl e.fvarId! fun l => l.setType e') ctx
            withLCtx ctx' #[] do mkLambdaFVars xs (← visit b)
        | Expr.forallE ..    => forallTelescope e fun xs b => do 
          if skipArgs then mkForallFVars xs (← visit b)
          else
            let ctx ← getLCtx
            let ctx' ← xs.foldlM (fun ctx' e => do
              let e' ← visit (ctx'.getFVar! e).type
              return ctx'.modifyLocalDecl e.fvarId! fun l => l.setType e') ctx
            withLCtx ctx' #[] do mkForallFVars xs (← visit b)
        | Expr.proj n i s .. => return mkProj n i (← visit s)
        | _                  => return e
  visit e |>.run

def reallyReduceAll (e : Expr) : MetaM Expr :=
  reallyReduce e false false false

syntax (name := reallyReduceCmd) "#reallyReduce " term : command

open Elab Command in
@[command_elab reallyReduceCmd] def elabReallyReduce : CommandElab
  | `(#reallyReduce%$tk $term) => go tk term
  | _ => throwUnsupportedSyntax
where
  go (tk : Syntax) (term : Syntax) : CommandElabM Unit :=
    withoutModifyingEnv <| runTermElabM fun _ => Term.withDeclName `_reduce do
      let e ← Term.elabTerm term none
      Term.synthesizeSyntheticMVarsNoPostponing
      let e ← Term.levelMVarToParam (← instantiateMVars e)
      -- TODO: add options or notation for setting the following parameters
      withTheReader Core.Context (fun ctx => { ctx with options := ctx.options.setBool `smartUnfolding false }) do
        let e ← withTransparency (mode := TransparencyMode.all) <| reallyReduce e false false false false
        logInfoAt tk e

#reduce (proofs := true) (types := true) 1 + 1 = 2 → True
#reallyReduce 1 + 1 = 2 → True

elab "rreduce" loc?:(ppSpace Parser.Tactic.location)? : tactic =>
  Mathlib.Tactic.runDefEqTactic (fun _ e => reallyReduce e (skipTypes := false) (skipProofs := false) (skipArgs := false)) loc? "rreduce"
