/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.Module
import DataflowRewriter.ExprLow

namespace DataflowRewriter

structure Connection (Ident : Type _) where
  output : InternalPort Ident
  input  : InternalPort Ident
  deriving Repr, Hashable, DecidableEq, Ord, Inhabited

structure ExprHigh (Ident : Type _) where
  modules     : IdentMap Ident Ident
  connections : List (Connection Ident)

instance (Ident) [ToString Ident] : ToString (ExprHigh Ident) where
  toString a :=
    let instances :=
      a.modules.foldl (λ s inst mod => s ++ s!"\n {inst} [mod = \"{mod}\"];") ""
    -- let inPorts :=
    --   a.inPorts.foldl
    --     (λ s i port => s ++ s!"\n {repr i} -> {repr port.inst}"
    --                      ++ s!" [inp = \"{repr port.name}\"];") ""
    -- let outPorts :=
    --   a.outPorts.foldl
    --     (λ s i port => s ++ s!"\n {repr port.inst} -> {repr i} "
    --                      ++ s!"[out = \"{repr port.name}\"];") ""
    let connections :=
      a.connections.foldl 
        (λ s => λ | ⟨ oport, iport ⟩ => 
                    s ++ s!"\n {oport.inst} -> {iport.inst} " 
                      ++ s!"[out = \"{oport.name}\"," 
                      ++ s!" inp = \"{iport.name}\"];") ""
    s!"[graph| {instances} {connections}\n ]"

namespace ExprHigh

variable {Ident : Type _}

def lower {Ident} (e : ExprHigh Ident) : Option (ExprLow Ident) :=
  match e.modules.toList with
  | x :: xs =>
    let prod_expr := xs.foldl (fun expr val => .product (.base val.1 val.2) expr) (.base x.1 x.2)
    let conn_expr := e.connections.foldl (fun expr conn => .connect conn.output conn.input expr) prod_expr
    let in_ports_conn := e.inPorts.foldl (fun expr i port => .input port i expr) conn_expr
    some <| e.outPorts.foldl (fun expr i port => .output port i expr) in_ports_conn
  | _ => none

variable [DecidableEq Ident]
variable [Inhabited Ident]

def subgraph (e : ExprHigh Ident) (instances : List Ident)
    (newInputs newOutputs : IdentMap Ident (InternalPort Ident)) : ExprHigh Ident :=
  { inPorts := (e.inPorts.filter (λ _ b => b.inst.elem instances)).append newInputs,
    outPorts := (e.outPorts.filter (λ _ b => b.inst.elem instances)).append newOutputs,
    modules := e.modules.filter (λ b _ => b ∈ instances),
    connections :=
      e.connections.filter λ a =>  
        a.input.inst.elem instances && a.output.inst.elem instances 
  }

def subgraph' (e : ExprHigh Ident) (instances : List Ident)
    (newInputs newOutputs : IdentMap Ident (InternalPort Ident)) : ExprHigh Ident :=
  e.subgraph (e.modules.keysList.diff instances)
    (newOutputs.mapVal λ _ v => ((e.connections.find? λ | ⟨ o, _ ⟩ => v = o).getD default).input)
    (newInputs.mapVal λ _ v => ((e.connections.find? λ | ⟨ _, i ⟩ => v = i).getD default).output)

def subgraph'' (e : ExprHigh Ident) (instances : List Ident)
    (newInputs newOutputs : IdentMap Ident (InternalPort Ident)) : ExprHigh Ident :=
  e.subgraph (e.modules.keysList.diff instances) newInputs newOutputs

def inline (e e' : ExprHigh Ident) : Option (ExprHigh Ident) := do
  let new_input_connections ← e'.inPorts.foldlM (λ conns i port => do
                                                    let outP ← e.outPorts.find? i
                                                    return Connection.mk port outP :: conns) []
  let new_output_connections ← e'.outPorts.foldlM (λ conns i port => do
                                                    let inpP ← e.inPorts.find? i
                                                    return Connection.mk inpP port :: conns) []
  return { inPorts := e.inPorts.filter (λ a _ => a ∉ e'.outPorts.keysList),
           outPorts := e.outPorts.filter (λ a _ => a ∉ e'.inPorts.keysList),
           modules := e.modules.append e'.modules,
           connections := e.connections
                          ++ new_input_connections
                          ++ new_output_connections
                          ++ e'.connections
         }

end ExprHigh

declare_syntax_cat dot_value
declare_syntax_cat dot_stmnt
declare_syntax_cat dot_attr_list
declare_syntax_cat dot_attr

syntax str : dot_value
syntax num : dot_value
syntax ident : dot_value

syntax ident " = " dot_value : dot_attr
syntax (dot_attr),* : dot_attr_list

syntax ident (" [" dot_attr_list "]")? : dot_stmnt
syntax ident " -> " ident (" [" dot_attr_list "]")? : dot_stmnt

syntax dot_stmnt_list := (dot_stmnt "; ")*

syntax dot_input_list := ("(" ident ", " num ")"),*

syntax (name := dot_graph) "[graph| " dot_stmnt_list " ]" : term

open Lean.Meta Lean.Elab Term Lean.Syntax

open Lean in
def findStx (n : Name) (stx : Array Syntax) : Option Nat := do
  let mut out := none
  for pair in stx do
    if pair[0].getId = n then
      out := some (TSyntax.mk pair[2][0]).getNat
  out

open Lean in
def findStxStr (n : Name) (stx : Array Syntax) : MetaM (Option String) := do
  let mut out := none
  for pair in stx do
    if pair[0].getId = n then
      let some out' := pair[2][0].isStrLit?
        | throwErrorAt pair[2][0] "`mod` attribute is not a string"
      out := some out'
  return out

def toInstIdent {α} [Inhabited α] (n : String) (h : Std.HashMap String α) : InstIdent α :=
  match n with
  | "io" => .top
  | s => .internal h[s]!

open Lean Qq in
@[term_elab dot_graph]
def dotGraphElab : TermElab := λ stx _typ? => do
  let mut idx := 1
  let mut idx' := 0
  let mut hmap : Std.HashMap Name String := ∅
  let mut instMap : Std.HashMap Name (String × InstIdent Nat) := ∅
  let mut revInstMap : Std.HashMap Nat Name := ∅
  let mut modMap : Std.HashMap String Nat := ∅
  let mut conns : List (Connection Nat) := []
  for stmnt in stx[1][0].getArgs do
    let low_stmnt := stmnt.getArgs[0]!
    match low_stmnt with
    -- | `(dot_stmnt| $i:ident $[[$[$el:dot_attr],*]]? ) =>
    | `(dot_stmnt| $i:ident $[[$[$el:dot_attr],*]]? ) =>
      let some el := el
        | throwErrorAt i "No `mod` attribute found at node"
      let some modId ← findStxStr `mod el
        | throwErrorAt i "No `mod` attribute found at node"
      let mut modInst : InstIdent Nat := .top
      unless modId == "io" do modInst := .internal idx
      let (b, map') := instMap.containsThenInsertIfNew i.getId (modId, modInst)
      if !b then
        instMap := map'
        -- instMap := instMap.insert i.getId idx
        -- revInstMap := revInstMap.insert idx i.getId
        idx := idx + 1
      else 
        logWarning s!"Multiple references to {i.getId} found"
      let (b, modMap') := modMap.containsThenInsertIfNew modId idx'
      if !b then
        modMap := modMap'
        idx' := idx' + 1
      -- logInfo m!"{el.map (·.get! 1 |>.raw.getArgs.get! 0)}"
    | `(dot_stmnt| $a:ident -> $b:ident $[[$[$el:dot_attr],*]]? ) =>
      let some el := el
        | throwErrorAt (mkListNode #[a, b]) "No `mod` attribute found at node"
      let mut out := (findStx `out el) -- | throwErrorAt (mkListNode el) "No input found"
      let mut inp := (findStx `inp el) -- | throwErrorAt (mkListNode el) "No output found"
      if out.isNone && hmap[a.getId]! == "io" then out := some 0
      if inp.isNone && hmap[b.getId]! == "io" then inp := some 0
      let some out' := out | throwErrorAt (mkListNode el) "No output found"
      let some inp' := inp | throwErrorAt (mkListNode el) "No input found"
      -- logInfo m!"out = {out}, in = {inp}"
      conns := ⟨ ⟨ instMap[a.getId]!.snd, out' ⟩, ⟨ instMap[b.getId]!.snd, inp' ⟩ ⟩ :: conns
    | _ => pure ()
  -- logInfo m!"{lst}"
  let internalConns := 
    conns.filterMap (fun | ⟨ ⟨ .internal nx, x ⟩, ⟨ .internal ny, y ⟩⟩ => 
                           .some ((nx, x), (ny, y))
                         | _ => .none)
  let inputConns := 
    conns.filterMap (fun | ⟨ ⟨ .top, x ⟩, ⟨ .internal ny, y ⟩⟩ => .some (x, (ny, y))
                         | _ => .none)
  let outputConns := 
    conns.filterMap (fun | ⟨ ⟨ .internal nx, x ⟩, ⟨ .top, y⟩⟩ => .some ((nx, x), y)
                         | _ => .none)
  let connExpr : Q(List (Connection Nat)) ← mkListLit q(Connection Nat) (← internalConns.mapM (λ ⟨ ⟨ a, b ⟩, ⟨ c, d ⟩ ⟩ => do
    let idents : Array Q(Nat) := #[a, b, c, d].map (.natVal · |> .lit)
    let inPort : Q(InternalPort Nat) := q(InternalPort.mk (.internal $(idents[0]!)) $(idents[1]!))
    let outPort : Q(InternalPort Nat) := q(InternalPort.mk (.internal $(idents[2]!)) $(idents[3]!))
    mkAppM ``Connection.mk #[inPort, outPort]))
  let inputPorts : Q(List (Nat × InternalPort Nat)) ← mkListLit q(Nat × InternalPort Nat) (← inputConns.mapM (λ ⟨ a, ⟨ c, d ⟩ ⟩ => do
    let idents : Array Q(Nat) := #[a, c, d].map (.natVal · |> .lit)
    let ioPort := idents[0]!
    let outPort : Q(InternalPort Nat) := q(InternalPort.mk (.internal $(idents[1]!)) $(idents[2]!))
    return q(($ioPort, $outPort))))
  let outputPorts : Q(List (Nat × InternalPort Nat)) ← mkListLit q(Nat × InternalPort Nat) (← outputConns.mapM (λ ⟨ ⟨ a, b ⟩, d ⟩ => do
    let idents : Array Q(Nat) := #[a, b, d].map (.natVal · |> .lit)
    let ioPort := idents[2]!
    let outPort : Q(InternalPort Nat) := q(InternalPort.mk (.internal $(idents[0]!)) $(idents[1]!))
    return q(($ioPort, $outPort))))
  let modList : Q(List (String × Nat)) ← mkListLit (← mkAppM ``Prod #[mkConst ``Nat, mkConst ``Nat])
    (← hmap.toList.mapM (fun (a, b) => mkAppM ``Prod.mk #[.lit (.strVal instMap[a]!.fst), .lit (.natVal modMap[b]!)]))
  let modListMap : Q(IdentMap Nat Nat) := q(List.toAssocList $modList)
  return q(ExprHigh.mk $modListMap (List.toAssocList $inputPorts)
                       (List.toAssocList $outputPorts) $connExpr)

open Lean.PrettyPrinter Delaborator SubExpr

namespace mergemod

def mergeHigh : ExprHigh Nat :=
  [graph|
    src0 [mod="io"];
    snk0 [mod="io"];

    fork1 [mod="fork"];
    fork2 [mod="fork"];
    merge1 [mod="merge"];
    merge2 [mod="merge"];

    src0 -> fork1 [inp="inp"];

    fork1 -> fork2 [out="out1",inp="inp"];

    fork1 -> merge1 [out="out2",inp="inp1"];
    fork2 -> merge1 [out="out1",inp="inp2"];
    fork2 -> merge2 [out="out2",inp="inp1"];

    merge1 -> merge2 [out="out",inp="inp2"];

    merge2 -> snk0 [out="out"];
  ]

open Lean Meta PrettyPrinter Delaborator SubExpr in
def unexpandStrProdList : Syntax → UnexpandM (TSyntax `DataflowRewriter.dot_stmnt_list)
  | `([$[($as:str, $bs:str)],*]) =>
    `(dot_stmnt_list| $[ $(as.map (mkIdent <| ·.getString.toName)):ident [mod=$bs:str] ; ]* )
  | _ => throw ()

open Lean Meta PrettyPrinter Delaborator SubExpr in
def unexpandStrInpList : Syntax → UnexpandM (TSyntax `DataflowRewriter.dot_stmnt_list)
  | `([$[($as:str, { inst := $bs:str, name := $cs:str })],*]) =>
    let as' := as.map (mkIdent <| ·.getString.toName)
    let bs' := bs.map (mkIdent <| ·.getString.toName)
    `(dot_stmnt_list| $[ $as':ident -> $bs':ident [inp=$cs:str] ; ]* )
  | _ => throw ()

open Lean Meta PrettyPrinter Delaborator SubExpr in
def unexpandStrOutList : Syntax → UnexpandM (TSyntax `DataflowRewriter.dot_stmnt_list)
  | `([$[($as:str, { inst := $bs:str, name := $cs:str })],*]) =>
    let as' := as.map (mkIdent <| ·.getString.toName)
    let bs' := bs.map (mkIdent <| ·.getString.toName)
    `(dot_stmnt_list| $[ $bs':ident -> $as':ident [out = $cs:str] ; ]* )
  | _ => throw ()

open Lean Meta PrettyPrinter Delaborator SubExpr in
def unexpandStrConnsList : Syntax → UnexpandM (TSyntax `DataflowRewriter.dot_stmnt_list)
  | `([$[{ output := { inst := $as:str, name := $bs:str }
           , input := { inst := $cs:str, name := $ds:str }}],*]) =>
    let as' := as.map (mkIdent <| ·.getString.toName)
    let cs' := cs.map (mkIdent <| ·.getString.toName)
    `(dot_stmnt_list| $[ $as':ident -> $cs':ident [out = $bs:str, inp = $ds:str] ; ]* )
  | _ => throw ()

open Lean Meta PrettyPrinter Delaborator SubExpr in
def runUnexpander {α} (f : Syntax → UnexpandM α) (s : Syntax) : DelabM α := do
  match f s |>.run (← getRef) |>.run () with
    | EStateM.Result.ok stx _ => return stx
    | _ => failure

open Lean Meta PrettyPrinter Delaborator SubExpr in
def combineDotStmntList (a b : TSyntax `DataflowRewriter.dot_stmnt_list) : DelabM (TSyntax `DataflowRewriter.dot_stmnt_list) :=
  match a, b with
  | `(dot_stmnt_list| $[$a ;]*), `(dot_stmnt_list| $[$b ;]*) =>
    `(dot_stmnt_list| $[$a ;]* $[$b ;]*)
  | _, _ => failure

open Lean Meta PrettyPrinter Delaborator SubExpr in
@[delab app.DataflowRewriter.ExprHigh.mk]
def delabExprHigh : Delab := do
  let modList ← withNaryArg 0 <| withNaryArg 2 do
    runUnexpander unexpandStrProdList (← delab)
  let inPorts ← withNaryArg 1 <| withNaryArg 2 do
    runUnexpander unexpandStrInpList (← delab)
  let outPorts ← withNaryArg 2 <| withNaryArg 2 do
    runUnexpander unexpandStrOutList (← delab)
  let conns ← withNaryArg 3 do
    runUnexpander unexpandStrConnsList (← delab)
  let combined ← #[inPorts, outPorts, conns].foldlM combineDotStmntList modList
  `([graph| $combined ])

#eval [graph|
    src0 [mod="io"];
    snk0 [mod="io"];

    fork1 [mod="fork"];
    fork2 [mod="fork"];
    merge1 [mod="merge"];
    merge2 [mod="merge"];

    src0 -> fork1 [inp="inp"];

    fork1 -> fork2 [out="out1",inp="inp"];

    fork1 -> merge1 [out="out2",inp="inp1"];
    fork2 -> merge1 [out="out1",inp="inp2"];
    fork2 -> merge2 [out="out2",inp="inp1"];

    merge1 -> merge2 [out="out",inp="inp2"];

    merge2 -> snk0 [out="out"];
  ]
#check [graph|
    src0 [mod="io"];
    snk0 [mod="io"];

    fork1 [mod="fork"];
    fork2 [mod="fork"];
    merge1 [mod="merge"];
    merge2 [mod="merge"];

    src0 -> fork1 [inp="inp"];

    fork1 -> fork2 [out="out1",inp="inp"];

    fork1 -> merge1 [out="out2",inp="inp1"];
    fork2 -> merge1 [out="out1",inp="inp2"];
    fork2 -> merge2 [out="out2",inp="inp1"];

    merge1 -> merge2 [out="out",inp="inp2"];

    merge2 -> snk0 [out="out"];
  ]

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

end mergemod

end DataflowRewriter
