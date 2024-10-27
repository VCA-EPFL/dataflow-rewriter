/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.Module
import DataflowRewriter.ExprHigh
import DataflowRewriter.ExprLowLemmas
import DataflowRewriter.ExprHighElaborator

namespace DataflowRewriter

namespace Module

variable {Ident : Type _}

def liftGraph {S} (m : Module Ident S) (p : PortMapping Ident) (inst typ : Ident) : ExprHigh Ident :=
  { modules := [(inst, p, typ)].toAssocList
    connections := []
  }

end Module

namespace ExprHigh

section Semantics

variable {Ident}
variable [DecidableEq Ident]

variable (ε : IdentMap Ident ((T: Type) × Module Ident T))

@[drunfold] def build_module' (e : ExprHigh Ident) : Option (Σ T, Module Ident T) :=
  e.lower.bind (·.build_module ε)

@[drunfold] def build_moduleP (e : ExprHigh Ident)
    (h : (build_module' ε e).isSome = true := by rfl)
    : Σ T, Module Ident T :=
  e.build_module' ε |>.get h

@[drunfold] def build_module (e : ExprHigh Ident) : Σ T, Module Ident T :=
  e.build_module' ε |>.getD ⟨ Unit, Module.empty _ ⟩

@[drunfold] abbrev build_module_expr (ε : IdentMap Ident (Σ T, Module Ident T))
    (e : ExprHigh Ident)
    : Module Ident (e.build_module ε).1 := (e.build_module ε).2

@[drunfold] abbrev build_module_type (ε : IdentMap Ident (Σ T, Module Ident T))
    (e : ExprLow Ident)
    : Type _ := (e.build_module ε).1

notation:25 "[Ge| " e ", " ε " ]" => build_module_expr ε e
notation:25 "[GT| " e ", " ε " ]" => build_module_type ε e

end Semantics

end ExprHigh

namespace Testing

def threemerge T : StringModule (List T) :=
  { inputs := [(⟨.internal "merge1", "0"⟩, ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩),
               (⟨.internal "merge1", "1"⟩, ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩),
               (⟨.internal "merge2", "1"⟩, ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩)].toAssocList,
    outputs := [(⟨.internal "merge2", "0"⟩, ⟨ T, λ oldList oldElement newList => ∃ i, newList = oldList.remove i ∧ oldElement = oldList.get i ⟩)].toAssocList,
    internals := []
  }

#eval mergeHigh.replace ["merge1", "merge2"] ((threemerge Nat).liftGraph ∅ "m" "merge3") |>.get rfl
  |>.rename "merge3" (⟨[ (⟨.internal "merge2", "0"⟩, ⟨.internal "mod0", "2"⟩)
                       , (⟨.internal "merge1", "0"⟩, ⟨.internal "mod0", "0"⟩)
                       , (⟨.internal "merge1", "1"⟩, ⟨.internal "mod0", "1"⟩)].toAssocList,
                       [ (⟨.internal "merge2", "0"⟩, ⟨.internal "mod0", "0"⟩) ].toAssocList ⟩)
  |> IO.println

-- #eval mergeHigh.lower.get rfl |>.higher


-- open Lean Meta PrettyPrinter Delaborator SubExpr in
-- def unexpandStrProdList : Syntax → UnexpandM (TSyntax `DataflowRewriter.dot_stmnt_list)
-- | `([$[($as:str, $bs:str)],*]) =>
--   `(dot_stmnt_list| $[ $(as.map (mkIdent <| ·.getString.toName)):ident [mod=$bs:str] ; ]* )
-- | _ => throw ()

-- open Lean Meta PrettyPrinter Delaborator SubExpr in
-- def unexpandStrInpList : Syntax → UnexpandM (TSyntax `DataflowRewriter.dot_stmnt_list)
-- | `([$[($as:str, { inst := $bs:str, name := $cs:str })],*]) =>
--   let as' := as.map (mkIdent <| ·.getString.toName)
--   let bs' := bs.map (mkIdent <| ·.getString.toName)
--   `(dot_stmnt_list| $[ $as':ident -> $bs':ident [inp=$cs:str] ; ]* )
-- | _ => throw ()

-- open Lean Meta PrettyPrinter Delaborator SubExpr in
-- def unexpandStrOutList : Syntax → UnexpandM (TSyntax `DataflowRewriter.dot_stmnt_list)
-- | `([$[($as:str, { inst := $bs:str, name := $cs:str })],*]) =>
--   let as' := as.map (mkIdent <| ·.getString.toName)
--   let bs' := bs.map (mkIdent <| ·.getString.toName)
--   `(dot_stmnt_list| $[ $bs':ident -> $as':ident [out = $cs:str] ; ]* )
-- | _ => throw ()

-- open Lean Meta PrettyPrinter Delaborator SubExpr in
-- def unexpandStrConnsList : Syntax → UnexpandM (TSyntax `DataflowRewriter.dot_stmnt_list)
-- | `([$[{ output := { inst := $as:str, name := $bs:str }
--          , input := { inst := $cs:str, name := $ds:str }}],*]) =>
--   let as' := as.map (mkIdent <| ·.getString.toName)
--   let cs' := cs.map (mkIdent <| ·.getString.toName)
--   `(dot_stmnt_list| $[ $as':ident -> $cs':ident [out = $bs:str, inp = $ds:str] ; ]* )
-- | _ => throw ()

-- open Lean Meta PrettyPrinter Delaborator SubExpr in
-- def runUnexpander {α} (f : Syntax → UnexpandM α) (s : Syntax) : DelabM α := do
--   match f s |>.run (← getRef) |>.run () with
--   | EStateM.Result.ok stx _ => return stx
--   | _ => failure

-- open Lean Meta PrettyPrinter Delaborator SubExpr in
-- def combineDotStmntList (a b : TSyntax `DataflowRewriter.dot_stmnt_list) : DelabM (TSyntax `DataflowRewriter.dot_stmnt_list) :=
--   match a, b with
--   | `(dot_stmnt_list| $[$a ;]*), `(dot_stmnt_list| $[$b ;]*) =>
--     `(dot_stmnt_list| $[$a ;]* $[$b ;]*)
--   | _, _ => failure

-- open Lean Meta PrettyPrinter Delaborator SubExpr in
-- @[delab app.DataflowRewriter.ExprHigh.mk]
-- def delabExprHigh : Delab := do
--   let modList ← withNaryArg 0 <| withNaryArg 2 do
--     runUnexpander unexpandStrProdList (← delab)
--   let inPorts ← withNaryArg 1 <| withNaryArg 2 do
--     runUnexpander unexpandStrInpList (← delab)
--   let outPorts ← withNaryArg 2 <| withNaryArg 2 do
--     runUnexpander unexpandStrOutList (← delab)
--   let conns ← withNaryArg 3 do
--     runUnexpander unexpandStrConnsList (← delab)
--   let combined ← #[inPorts, outPorts, conns].foldlM combineDotStmntList modList
--   `([graph| $combined ])

-- #eval [graph|
--     src0 [mod="io"];
--     snk0 [mod="io"];

--     fork1 [mod="fork"];
--     fork2 [mod="fork"];
--     merge1 [mod="merge"];
--     merge2 [mod="merge"];

--     src0 -> fork1 [inp="inp"];

--     fork1 -> fork2 [out="out1",inp="inp"];

--     fork1 -> merge1 [out="out2",inp="inp1"];
--     fork2 -> merge1 [out="out1",inp="inp2"];
--     fork2 -> merge2 [out="out2",inp="inp1"];

--     merge1 -> merge2 [out="out",inp="inp2"];

--     merge2 -> snk0 [out="out"];
--   ]
-- #check [graph|
--     src0 [mod="io"];
--     snk0 [mod="io"];

--     fork1 [mod="fork"];
--     fork2 [mod="fork"];
--     merge1 [mod="merge"];
--     merge2 [mod="merge"];

--     src0 -> fork1 [inp="inp"];

--     fork1 -> fork2 [out="out1",inp="inp"];

--     fork1 -> merge1 [out="out2",inp="inp1"];
--     fork2 -> merge1 [out="out1",inp="inp2"];
--     fork2 -> merge2 [out="out2",inp="inp1"];

--     merge1 -> merge2 [out="out",inp="inp2"];

--     merge2 -> snk0 [out="out"];
--   ]

-- def mergeHighSubgraph := mergeHigh.subgraph ["merge1"] (RBMap.ofList [("merge1_a", ⟨"merge1", "inp1"⟩), ("merge1_b", ⟨"merge1", "inp2"⟩)] _)
--   (RBMap.ofList [("merge1_c", ⟨"merge1", "out"⟩)] _)

-- def mergeHighSubgraph' := mergeHigh.subgraph' ["merge1"] (RBMap.ofList [("merge1_a", ⟨"merge1", "inp1"⟩), ("merge1_b", ⟨"merge1", "inp2"⟩)] _)
--   (RBMap.ofList [("merge1_c", ⟨"merge1", "out"⟩)] _)

-- open Lean Meta PrettyPrinter Delaborator SubExpr in
-- elab "#delab" e:term : command => do
--   let l ← Command.liftTermElabM do
--     instantiateMVars <| (← Term.elabTerm e none)
--   logInfo (repr l)

-- #eval mergeHighSubgraph
-- #check ({ modules := RBMap.ofList [("merge1", "merge")] _,
--           inPorts := RBMap.ofList [("merge1_a", { inst := "merge1", name := "inp1" }),
--                       ("merge1_b", { inst := "merge1", name := "inp2" })] _,
--           outPorts := RBMap.ofList [("merge1_c", { inst := "merge1", name := "out" })] _,
--           connections := [] } : ExprHigh)
-- #eval mergeHighSubgraph'
-- #check ({ modules := RBMap.ofList [("fork1", "fork"), ("fork2", "fork"), ("merge2", "merge"), ("snk0", "io"), ("src0", "io")] _,
--           inPorts := RBMap.ofList [("merge1_c", { inst := "merge2", name := "inp2" }),
--                       ("src0", { inst := "fork1", name := "inp" })] _,
--           outPorts := RBMap.ofList [("merge1_a", { inst := "fork1", name := "out2" }),
--                        ("merge1_b", { inst := "fork2", name := "out1" }),
--                        ("snk0", { inst := "merge2", name := "out" })] _,
--           connections := [{ output := { inst := "fork2", name := "out2" }, input := { inst := "merge2", name := "inp1" } },
--                   { output := { inst := "fork1", name := "out1" }, input := { inst := "fork2", name := "inp" } }] } : ExprHigh)

-- #eval mergeHigh
-- #check ({ modules := RBMap.ofList [("fork1", "fork"),
--               ("fork2", "fork"),
--               ("merge1", "merge"),
--               ("merge2", "merge"),
--               ("snk0", "io"),
--               ("src0", "io")] _,
--            inPorts := RBMap.ofList [("snk0", { inst := "merge2", name := "out" })] _,
--            outPorts := RBMap.ofList [("src0", { inst := "fork1", name := "inp" })] _,
--            connections := [{ input := { inst := "merge2", name := "inp2" }, output := { inst := "merge1", name := "out" } },
--                   { input := { inst := "merge2", name := "inp1" }, output := { inst := "fork2", name := "out2" } },
--                   { input := { inst := "merge1", name := "inp2" }, output := { inst := "fork2", name := "out1" } },
--                   { input := { inst := "merge1", name := "inp1" }, output := { inst := "fork1", name := "out2" } },
--                   { input := { inst := "fork2", name := "inp" }, output := { inst := "fork1", name := "out1" } }] } : ExprHigh)

-- #eval mergeHighSubgraph'.inline mergeHighSubgraph
-- #check ({ modules := RBMap.ofList [("fork1", "fork"),
--               ("fork2", "fork"),
--               ("merge1", "merge"),
--               ("merge2", "merge"),
--               ("snk0", "io"),
--               ("src0", "io")] _,
--           inPorts := RBMap.ofList [("snk0", { inst := "merge2", name := "out" })] _,
--           outPorts := RBMap.ofList [("src0", { inst := "fork1", name := "inp" })] _,
--           connections := [{ input := { inst := "merge2", name := "inp1" }, output := { inst := "fork2", name := "out2" } },
--                   { input := { inst := "fork2", name := "inp" }, output := { inst := "fork1", name := "out1" } },
--                   { input := { inst := "merge1", name := "inp2" }, output := { inst := "fork2", name := "out1" } },
--                   { input := { inst := "merge1", name := "inp1" }, output := { inst := "fork1", name := "out2" } },
--                   { input := { inst := "merge2", name := "inp2" }, output := { inst := "merge1", name := "out" } }] } : ExprHigh)

end Testing

end DataflowRewriter
