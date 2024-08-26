import DataflowRewriter.Module

namespace DataflowRewriterTest

#eval merge3

#eval lower [ ("merge", ⟨ 2, 1 ⟩) ].toAssocList merge3

def merge3 : ExprHigh :=
  {[graph|
    merge1 [mod = "merge"];
    merge2 [mod = "merge"];
    merge1 -> merge2;
  ] with ioPorts := [ ("merge1", {(default : IOPort) with inPorts := [0, 1]})
                    , ("merge2", {inPorts := [1], outPorts := [0]})
                    ]}

def highlow int mod := do
  higher int <| ← lower int mod

#eval highlow [ ("merge", ⟨ 2, 1 ⟩) ].toAssocList merge3

#check List
#eval mergeHigh.subgraph ["fork1", "fork2"]
#check List.filter
#eval mergeHigh

def modules : IdentMap ((T : Type _) × Module T) :=
  [ ("io", ⟨ _, io Nat ⟩)
  , ("merge", ⟨ _, merge Nat ⟩)
  , ("fork", ⟨ _, fork Nat ⟩)
  ].toAssocList

def mod_interfaces : IdentMap Interface := Interface.ofModules modules

def mergeLow : ExprLow := lower mod_interfaces mergeHigh |>.get rfl

def mergeOther : Option ((T : Type _) × Module T) :=
  build_module' mergeLow modules

end DataflowRewriterTest
