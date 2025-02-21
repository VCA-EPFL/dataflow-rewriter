/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.ExprHigh
import DataflowRewriter.DotParser
import DataflowRewriter.Rewriter
import DataflowRewriter.DynamaticPrinter
import DataflowRewriter.Rewrites.LoopRewrite
import DataflowRewriter.Rewrites.CombineBranch
import DataflowRewriter.Rewrites.CombineMux
import DataflowRewriter.Rewrites.JoinSplitLoopCond
import DataflowRewriter.Rewrites.ReduceSplitJoin

open Batteries (AssocList)

open DataflowRewriter

structure CmdArgs where
  outputFile : Option System.FilePath
  inputFile : Option System.FilePath
  logFile : Option System.FilePath
  logStdout : Bool
  noDynamaticDot : Bool
  parseOnly : Bool
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
"

def combineRewrites := [CombineMux.rewrite, CombineBranch.rewrite, JoinSplitLoopCond.rewrite, ReduceSplitJoin.rewrite]

def topLevel (e : ExprHigh String) : RewriteResult (ExprHigh String) :=
  rewrite_loop e combineRewrites (depth := 10000)

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
  let fileContents ← IO.FS.readFile parsed.inputFile.get!
  let (exprHigh, assoc) ← IO.ofExcept fileContents.toExprHigh

  let mut rewrittenExprHigh := exprHigh
  let mut st : List RewriteInfo := default

  if !parsed.parseOnly then
    match topLevel rewrittenExprHigh |>.run default with
    | .ok rewrittenExprHigh' st' => rewrittenExprHigh := rewrittenExprHigh'; st := st'
    | .error p st' => IO.eprintln p; st := st'

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
