import DataflowRewriter.ExprHigh
import DataflowRewriter.DotParser

open DataflowRewriter

def dotToExprHigh (d : Parser.DotGraph) : Except String (ExprHigh String) := do
  let mut maps : InstMaps := ⟨ ∅, ∅ ⟩
  maps ← d.nodes.foldlM (λ a (s, l) => do
      let some typ := l.find? (·.key = "mod")
        | throw "could not find instance type"
      let cluster := l.find? (·.key = "cluster") |>.getD ⟨"cluster", "false"⟩
      let .ok clusterB := Parser.parseBool.run cluster.value
        | throw "cluster could not be parsed"
      updateNodeMaps a s typ.value clusterB
    ) maps
  let (maps', conns) ← d.edges.foldlM (λ a (s1, s2, l) => do
      let inp := l.find? (·.key = "inp")
      let out := l.find? (·.key = "out")
      match updateConnMaps a.fst a.snd s1 s2 (inp.map (·.value)) (out.map (·.value)) with
      | .ok v => return v
      | .error s => throw s.toString
    ) (maps, [])
  return ⟨ maps'.instTypeMap.toList.toAssocList, conns ⟩

def main (args : List String) : IO Unit := do
  let [filename] := args | throw <| IO.userError "Expecting one argument, the input file"
  let fileContents ← IO.FS.readFile filename
  let exprHigh ← IO.ofExcept do
    let dotGraph ← Parser.dotGraph.run fileContents
    dotToExprHigh dotGraph
  IO.println exprHigh
