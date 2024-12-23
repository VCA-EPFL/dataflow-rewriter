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

open Batteries (AssocList)

open DataflowRewriter

structure CmdArgs where
  outputFile : Option System.FilePath
  inputFile : Option System.FilePath
  help : Bool
deriving Inhabited

def CmdArgs.empty : CmdArgs := ⟨none, none, false⟩

def parseArgs (args : List String) : Except String CmdArgs := go CmdArgs.empty args
  where
    go (c : CmdArgs) : List String → Except String CmdArgs
    | .cons "-h" _rst | .cons "--help" _rst => .ok {c with help := true}
    | .cons "-o" (.cons fp rst) | .cons "--output" (.cons fp rst) =>
      go {c with outputFile := some fp} rst
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
  -h, --help         Print this help text
  -o, --output FILE  Set output file
"

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
  IO.print (repr exprHigh)
  let rewrittenExprHigh ← IO.ofExcept <|
    ({CombineMux.rewrite "T" "T" with pattern := fun _ => pure ["phi_n0", "phiC_3", "fork_11_3"]}).run "rw1_" exprHigh
  -- let rewrittenExprHigh ← IO.ofExcept <|
  --   ({CombineMux.rewrite "T" "T" with pattern := fun _ => pure ["phi_n0", "phiC_3", "fork_11_3"]}).run "rw1_" rewrittenExprHigh
    -- pure exprHigh
  let some l := dynamaticString rewrittenExprHigh assoc.inverse
    | IO.eprintln s!"Failed to print ExprHigh: {rewrittenExprHigh}"
  match parsed.outputFile with
  | some ofile =>
    IO.FS.writeFile ofile l
  | none =>
    IO.println l
