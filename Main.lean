/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.ExprHigh
import DataflowRewriter.DotParser
import DataflowRewriter.Rewriter
import DataflowRewriter.Rewrites.MergeRewrite
import DataflowRewriter.Rewrites.ForkRewrite


open DataflowRewriter

def dotToExprHigh (d : Parser.DotGraph) : Except String (ExprHigh String) := do
  let mut maps : InstMaps := ⟨ ∅, ∅ ⟩
  maps ← d.nodes.foldlM (λ a (s, l) => do
      let some typ := l.find? (·.key = "type")
        | throw "could not find instance type"
      let cluster := l.find? (·.key = "cluster") |>.getD ⟨"cluster", "false"⟩
      let .ok clusterB := Parser.parseBool.run cluster.value
        | throw "cluster could not be parsed"
      updateNodeMaps a s typ.value clusterB
    ) maps
  let (maps', conns) ← d.edges.foldlM (λ a (s1, s2, l) => do
      let inp := l.find? (·.key = "inp")
      let out := l.find? (·.key = "out")
      match updateConnMaps a.fst a.snd s1 s2 (out.map (·.value)) (inp.map (·.value)) with
      | .ok v => return v
      | .error s => throw s.toString
    ) (maps, [])
  return ⟨ maps'.instTypeMap.toList.toAssocList, conns ⟩

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
  let exprHigh ← IO.ofExcept do
    let dotGraph ← Parser.dotGraph.run fileContents
    dotToExprHigh dotGraph
  let rewritenExprHigh ← IO.ofExcept <|
    rewrite_loop "rw" exprHigh [MergeRewrite.rewrite, ForkRewrite.rewrite] 100
  match parsed.outputFile with
  | some ofile =>
    IO.FS.writeFile ofile (toString rewritenExprHigh)
  | none =>
    IO.println <| toString rewritenExprHigh
