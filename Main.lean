/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.ExprHigh
import DataflowRewriter.DotParser
import DataflowRewriter.Rewriter
import DataflowRewriter.DynamaticPrinter
import DataflowRewriter.Rewrites
import DataflowRewriter.JSLang

open Batteries (AssocList)

open DataflowRewriter

structure CmdArgs where
  outputFile : Option System.FilePath
  inputFile : Option System.FilePath
  logFile : Option System.FilePath
  logStdout : Bool
  noDynamaticDot : Bool
  parseOnly : Bool
  graphitiOracle : Option String
  help : Bool
deriving Inhabited

def CmdArgs.empty : CmdArgs := default

def parseArgs (args : List String) : Except String CmdArgs := go CmdArgs.empty args
  where
    go (c : CmdArgs) : List String → Except String CmdArgs
    | .cons "-h" _rst | .cons "--help" _rst => .ok {c with help := true}
    | .cons "-o" (.cons fp rst) | .cons "--output" (.cons fp rst) =>
      go {c with outputFile := some fp} rst
    | .cons "-l" (.cons fp rst) | .cons "--log" (.cons fp rst) =>
      go {c with logFile := some fp} rst
    | .cons "--log-stdout" rst =>
      go {c with logStdout := true} rst
    | .cons "--no-dynamatic-dot" rst =>
      go {c with noDynamaticDot := true} rst
    | .cons "--parse-only" rst =>
      go {c with parseOnly := true} rst
    | .cons "--oracle" (.cons fp rst) =>
      go {c with graphitiOracle := fp} rst
    | .cons fp rst => do
      if "-".isPrefixOf fp then throw s!"argument '{fp}' not recognised"
      if c.inputFile.isSome then throw s!"more than one input file passed"
      go {c with inputFile := some fp} rst
    | [] => do
      if c.inputFile.isNone then throw s!"no input file passed"
      return c

def helpText : String :=
  "dataflow-rewriter -- v0.1.0

FORMAT
  dataflow-rewriter [OPTIONS...] FILE

OPTIONS
  -h, --help          Print this help text
  -o, --output FILE   Set output file
  -l, --log FILE      Set JSON log output
  --log-stdout        Set JSON log output to STDOUT
  --no-dynamatic-dot  Don't output dynamatic DOT, instead output the raw
                      dot that is easier for debugging purposes.
  --parse-only        Only parse the input without performing rewrites.
  --oracle            Path to the oracle executable.  Default is graphiti_oracle.
"

def combineRewrites := [CombineMux.rewrite, CombineBranch.rewrite, JoinSplitLoopCond.rewrite, LoadRewrite.rewrite]
def reduceRewrites := [ReduceSplitJoin.rewrite, JoinQueueLeftRewrite.rewrite, JoinQueueRightRewrite.rewrite, MuxQueueRightRewrite.rewrite]
def reduceSink := [SplitSinkRight.rewrite, SplitSinkLeft.rewrite, PureSink.rewrite]
def movePureJoin := [PureJoinLeft.rewrite, PureJoinRight.rewrite, PureSplitRight.rewrite, PureSplitLeft.rewrite]

def topLevel (e : ExprHigh String) : RewriteResult (ExprHigh String) := do
  let rw ← rewrite_loop e combineRewrites
  let rw ← rewrite_fix rw reduceRewrites
  let rw ← rewrite_fix rw (PureRewrites.specialisedPureRewrites LoopRewrite.nonPureMatcher)
  -- let rw ← rewrite_fix rw [ForkPure.rewrite]
  let rw ← rewrite_fix rw <| [ForkPure.rewrite, ForkJoin.rewrite] ++ movePureJoin ++ reduceSink  -- (JoinPureUnit.rewrite :: movePureJoin) ++ reduceSink
  let rw ← rewrite_fix rw (PureRewrites.specialisedPureRewrites LoopRewrite.nonPureForkMatcher)
  let rw ← rewrite_fix rw ([PureSeqComp.rewrite] ++ movePureJoin ++ reduceSink)
  -- let rw ← JoinComm.targetedRewrite "rw_f19_l1__R_1" |>.run "ranodm_" rw
  return rw

def pureGenerator' (g : ExprHigh String) : List JSLangRewrite → Nat → RewriteResult (ExprHigh String)
| _, 0 => throw <| .error "No fuel"
| [], _ => pure g
| [jsRw], _ => do
  let rw ← jsRw.mapToRewrite.run "jsrw_1_" g
  let rw ← rewrite_fix rw ([PureSeqComp.rewrite] ++ movePureJoin ++ reduceSink)
  return rw
| jsRw :: rst, fuel+1 => do
  addRewriteInfo {(default : RewriteInfo) with debug := .some s!"{repr jsRw}"}
  let rw ← jsRw.mapToRewrite.run s!"jsrw_{rst.length + 1}_" g
  let rst ← update_state JSLang.upd rst

  let (rw, rst) ← rewrite_fix_rename rw ([PureSeqComp.rewrite] ++ movePureJoin ++ reduceSink) JSLang.upd rst
  pureGenerator' rw rst fuel

def pureGenerator g js := pureGenerator' g js (js.length + 1)

def eggPureGenerator (fuel : Nat) (parsed : CmdArgs) (g : ExprHigh String) (st : List RewriteInfo) : IO (ExprHigh String × List RewriteInfo) := do
  match fuel with
  | 0 => throw <| .userError s!"{decl_name%}: no fuel"
  | fuel+1 =>
    let jsRw ← rewriteWithEgg (eggCmd := parsed.graphitiOracle.getD "graphiti_oracle") g
    if jsRw.length = 0 then return (g, st)
    IO.eprintln (repr jsRw)
    match pureGenerator g jsRw |>.run st with
    | .ok g' st' => eggPureGenerator fuel parsed g' st'
    | .error e st' =>
      match parsed.logFile with
      | .some lfile => IO.FS.writeFile lfile <| toString <| Lean.toJson st'
      | .none =>
        if parsed.logStdout then IO.println <| Lean.toJson st'
      IO.eprintln e
      IO.Process.exit 1

def renameAssoc (assoc : AssocList String (AssocList String String)) (r : RewriteInfo) : AssocList String (AssocList String String) :=
  assoc.mapKey (λ x => match r.renamed_input_nodes.find? x with
                       | .some (.some x') => x'
                       | _ => x)

def renameAssocAll assoc (rlist : List RewriteInfo) := rlist.foldl renameAssoc assoc

def main (args : List String) : IO Unit := do
  let parsed ←
    try IO.ofExcept <| parseArgs args
    catch
    | .userError s => do
      IO.eprintln ("error: " ++ s)
      IO.print helpText
      IO.Process.exit 1
    | e => throw e
  if parsed.help then
    IO.print helpText
    return
  let goracle := parsed.graphitiOracle.getD "graphiti_oracle"
  let fileContents ← IO.FS.readFile parsed.inputFile.get!
  let (exprHigh, assoc) ← IO.ofExcept fileContents.toExprHigh

  let mut rewrittenExprHigh := exprHigh
  let mut st : List RewriteInfo := default

  if !parsed.parseOnly then
    match topLevel rewrittenExprHigh |>.run default with
    | .ok rewrittenExprHigh' st' => rewrittenExprHigh := rewrittenExprHigh'; st := st'
    | .error p st' => IO.eprintln p; st := st'

    let (g', st') ← eggPureGenerator 100 parsed rewrittenExprHigh st
    rewrittenExprHigh := g'; st := st'

    match LoopRewrite2.rewrite.run "loop_rw_" rewrittenExprHigh |>.run default with
    | .ok g' st' => rewrittenExprHigh := g'; st := st'
    | .error p st' => IO.eprintln p; st := st'

    -- let .ok (bl, _) _ := LoopRewrite.boxLoopBody rewrittenExprHigh |>.run default | throw (.userError "could not find subgraph")

    -- match  (depth := 10000) |>.run st with
    -- | .ok rewrittenExprHigh' st' => rewrittenExprHigh := rewrittenExprHigh'; st := st'
    -- | .error p st' => IO.eprintln p; st := st'

  let some l :=
    if parsed.noDynamaticDot then pure (toString rewrittenExprHigh)
    else dynamaticString rewrittenExprHigh (renameAssocAll assoc st)
    | IO.eprintln s!"Failed to print ExprHigh: {rewrittenExprHigh}"

  match parsed.logFile with
  | .some lfile => IO.FS.writeFile lfile <| toString <| Lean.toJson st
  | .none =>
    if parsed.logStdout then IO.println <| Lean.toJson st

  match parsed.outputFile with
  | some ofile =>
    IO.FS.writeFile ofile l
  | none =>
    IO.println l

  -- let .ok (subgraph, _) _ := (LoopRewrite.boxLoopBody rewrittenExprHigh).run st | throw (.userError "could not find loop body")
  -- let .some (subgraph', _) := rewrittenExprHigh.extract subgraph | throw (.userError "could not generate subgraph")
  -- let subgraph' : ExprHigh String := ⟨subgraph'.1, subgraph'.2.filter (λ | c@⟨⟨.internal n, o⟩, ⟨.internal n', o'⟩⟩ => n ∈ subgraph'.1.keysList ∧ n' ∈ subgraph'.1.keysList
  --                                                                        | _ => false)⟩
