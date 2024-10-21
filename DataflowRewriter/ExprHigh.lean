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

/--
Graph description of a cicruit.  Note that currently one cannot describe an
input that connects directly to the output.  Instead, these always have to pass
by an internal module.
-/
structure ExprHigh (Ident : Type _) where
  modules     : IdentMap Ident (PortMapping Ident × Ident)
  connections : List (Connection Ident)
deriving Repr, DecidableEq, Inhabited

structure NamedExprHigh (Ident : Type _) where
  graph       : ExprHigh Ident
  inPorts     : IdentMap Ident (InternalPort Ident)
  outPorts    : IdentMap Ident (InternalPort Ident)

instance (Ident) [ToString Ident] : ToString (ExprHigh Ident) where
  toString a :=
    -- let instances :=
    --   a.modules.foldl (λ s inst mod => s ++ s!"\n {inst} [mod = \"{mod}\"];") ""
    let connections :=
      a.connections.foldl
        (λ s => λ | ⟨ oport, iport ⟩ =>
                    s ++ s!"\n {oport.inst} -> {iport.inst} "
                      ++ s!"[out = \"{oport.name}\","
                      ++ s!" inp = \"{iport.name}\"];") ""
    s!"[graph| {connections}\n ]"

namespace ExprHigh

variable {Ident : Type _}
variable [DecidableEq Ident]

@[drunfold] def lower (e : ExprHigh Ident) : Option (ExprLow Ident) :=
  match e.modules.toList with
  | x :: xs =>
    let prod_expr :=
      xs.foldl (λ expr val =>
          -- return .product (.base (int.toPortMapping val.1) val.2) expr)
          .product (Function.uncurry .base val.snd) expr)
        <| Function.uncurry .base x.snd
    return e.connections.foldl (λ expr conn => .connect conn.output conn.input expr) prod_expr
  | _ => none

variable [DecidableEq Ident]
variable [Inhabited Ident]

section Semantics

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

section Refinement

variable (ε : IdentMap Ident ((T : Type _) × Module Ident T))

/-
This one should be straight-forward due to `ExprLow.substitute_env`.
-/
theorem substitution₁ {I S} (mod : Module Ident I) (mod' : Module Ident S) g
    ident (h : ε.mem ident ⟨ I, mod ⟩) :
  mod ⊑ mod' →
  [Ge| g, ε ] ⊑ ([Ge| g, {ε | h := ⟨ S, mod' ⟩} ]) := by sorry

/-
This one should be straight-forward due to `ExprLow.substitution`.
-/
theorem substitution₄ {I S mod mod' i i' g} :
  ε.find? i = some ⟨ I, mod ⟩ →
  ε.find? i' = some ⟨ S, mod' ⟩ →
  mod ⊑ mod' →
  [Ge| g, ε ] ⊑ ([Ge| g.modify i i', ε ]) := by sorry

theorem substitution₅ {S mod l i i' g n m} :
  ε.find? i' = some ⟨ S, mod ⟩ →
  [Ge| g.subgraph l n m, ε ] ⊑ mod →
  [Ge| g, ε ] ⊑ ([Ge| g.abstract' l i i', ε ]) := by sorry

theorem substitution₆ {S mod l i i' g n m o} :
  ε.find? i' = some ⟨ S, mod ⟩ →
  mod ⊑ ([Ge| g.subgraph l n m, ε ]) →
  [Ge| g.concretise' o i, ε ] ⊑ ([Ge| g, ε ]) := by sorry

theorem substitution₇ {S mod i i' g'} {g : ExprHigh Ident} :
  ε.find? i' = some ⟨ S, mod ⟩ →
  mod ⊑ ([Ge| g', ε ]) →
  [Ge| g.abstract i i', ε ] ⊑ ([Ge| g.inlineD g', ε ]) := by sorry

theorem substitution₈ {S mod i i' g'} {g : ExprHigh Ident} :
  ε.find? i' = some ⟨ S, mod ⟩ →
  [Ge| g', ε ] ⊑ mod →
  [Ge| g.inlineD g', ε ] ⊑ ([Ge| g.abstract i i', ε ]) := by sorry

/-
`i` and `o` need to be constrained to have unique names w.r.t. the graph.
-/
theorem substitution₉ {l i o g g₁ g₂} :
  g.partition l i o = (g₁, g₂) →
  [Ge| g, ε ] ⊑ ([Ge| g₁.inlineD g₂, ε ]) := by sorry

/-
`i` and `o` need to be constrained to have unique names w.r.t. the graph.
-/
theorem substitution₁₀ {l i o g g₁ g₂} :
  g.partition l i o = (g₁, g₂) →
  [Ge| g₁.inlineD g₂, ε ] ⊑ ([Ge| g, ε ]) := by sorry

/-
`i` and `o` need to be constrained to have unique names w.r.t. the graph.
-/
theorem substitution₁₁ {l i o g g₁ g₂} :
  g.partition l i o = (g₁, g₂) →
  [Ge| g₁.inlineD g₂, ε ] ⊑ ([Ge| g, ε ]) := by sorry

theorem substitution₂ {I} (mod : Module Ident I) g i ident :
  ident ∉ ε.keysList →
  [Ge| i, ε ] ⊑ mod →
  [Ge| g.inlineD i, ε ] ⊑ ([Ge| g, ε.cons ident ⟨ I, mod ⟩ ]) := by sorry

theorem substitution₃ {I} (mod : Module Ident I) g i ident :
  ident ∉ ε.keysList →
  mod ⊑ ([Ge| i, ε ]) →
  [Ge| g, ε.cons ident ⟨ I, mod ⟩ ] ⊑ ([Ge| g.inlineD i, ε ]) := by sorry

theorem substitution (g i i' : ExprHigh Ident) :
  [Ge| i, ε ] ⊑ ([Ge| i', ε ]) →
  [Ge| g.inlineD i, ε ] ⊑ ([Ge| g.inlineD i', ε ]) := by sorry

end Refinement

end ExprHigh

class FreshIdent (Ident : Type _) where
  next : Ident → Ident

namespace ExprLow

variable {Ident : Type _}

def higher' [FreshIdent Ident] (fresh : Ident) : ExprLow Ident → (ExprHigh Ident × Ident)
| .base a b => (ExprHigh.mk [(fresh, (a, b))].toAssocList ∅, FreshIdent.next fresh)
| .connect o i e =>
  let (e', fresh') := e.higher' fresh
  ({e' with connections := e'.connections.cons ⟨ o, i ⟩}, fresh')
| .product e₁ e₂ =>
  let (e₁', fresh₁) := e₁.higher' fresh
  let (e₂', fresh₂) := e₂.higher' fresh₁
  (⟨ e₁'.1.append e₂'.1, e₁'.2.append e₂'.2 ⟩, fresh₂)

def higher [Inhabited Ident] [FreshIdent Ident] (e: ExprLow Ident) : ExprHigh Ident :=
  e.higher' default |>.fst

end ExprLow

namespace Module

variable {Ident : Type _}

def liftGraph {S} (m : Module Ident S) (inst typ : Ident) : ExprHigh Ident :=
  { modules := [(inst, typ)].toAssocList
    inPorts := m.inputs.foldl (λ | (nm : IdentMap Ident (InternalPort Ident)), ⟨.top, b⟩, _ =>
                                  nm.cons b ⟨.internal inst, b⟩
                                 | nm, _, _ => nm) ∅
    outPorts := m.outputs.foldl (λ | (nm : IdentMap Ident (InternalPort Ident)), ⟨.top, b⟩, _ =>
                                     nm.cons b ⟨.internal inst, b⟩
                                   | nm, _, _ => nm) ∅
    connections := []
  }

end Module

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
  let mut instMap : Std.HashMap Name (InstIdent String) := ∅
  let mut instTypeMap : Std.HashMap String String := ∅
  -- let mut modMap : Std.HashMap String Nat := ∅
  let mut conns : List (Connection String) := []
  for stmnt in stx[1][0].getArgs do
    let low_stmnt := stmnt.getArgs[0]!
    match low_stmnt with
    -- | `(dot_stmnt| $i:ident $[[$[$el:dot_attr],*]]? ) =>
    | `(dot_stmnt| $i:ident $[[$[$el:dot_attr],*]]? ) =>
      let some el := el
        | throwErrorAt i "No `mod` attribute found at node"
      let some modId ← findStxStr `mod el
        | throwErrorAt i "No `mod` attribute found at node"
      let mut modInst : InstIdent String := .top
      unless modId == "io" do
        modInst := .internal i.getId.toString
        -- let (b, modMap') := modMap.containsThenInsertIfNew modId idx'
        -- if !b then
        --   modMap := modMap'
      let (b, map') := instMap.containsThenInsertIfNew i.getId modInst
      if !b then
        instMap := map'
        -- instMap := instMap.insert i.getId idx
        -- revInstMap := revInstMap.insert idx i.getId
        unless modId == "io" do instTypeMap := instTypeMap.insert i.getId.toString modId
      else
        logWarning s!"Multiple references to {i.getId} found"
      -- logInfo m!"{el.map (·.get! 1 |>.raw.getArgs.get! 0)}"
    | `(dot_stmnt| $a:ident -> $b:ident $[[$[$el:dot_attr],*]]? ) =>
      let some el := el
        | throwErrorAt (mkListNode #[a, b]) "No `mod` attribute found at node"
      let mut out ← (findStxStr `out el) -- | throwErrorAt (mkListNode el) "No input found"
      let mut inp ← (findStxStr `inp el) -- | throwErrorAt (mkListNode el) "No output found"
      if out.isNone && instMap[a.getId]!.isTop then out := some "0"
      if inp.isNone && instMap[b.getId]!.isTop then inp := some "0"
      let some out' := out | throwErrorAt (mkListNode el) "No output found"
      let some inp' := inp | throwErrorAt (mkListNode el) "No input found"
      -- logInfo m!"out = {out}, in = {inp}"
      conns := ⟨ ⟨ instMap[a.getId]!, out' ⟩, ⟨ instMap[b.getId]!, inp' ⟩ ⟩ :: conns
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
  let connExpr : Q(List (Connection String)) ←
    mkListLit q(Connection String) (← internalConns.mapM (λ ⟨ ⟨ a, b ⟩, ⟨ c, d ⟩ ⟩ => do
      let idents : Array Q(String) := #[a, b, c, d].map (.strVal · |> .lit)
      let inPort : Q(InternalPort String) :=
        q(InternalPort.mk (.internal $(idents[0]!)) $(idents[1]!))
      let outPort : Q(InternalPort String) :=
        q(InternalPort.mk (.internal $(idents[2]!)) $(idents[3]!))
      mkAppM ``Connection.mk #[inPort, outPort]))
  let inputPorts : Q(List (String × InternalPort String)) ←
    mkListLit q(String × InternalPort String) (← inputConns.mapM (λ ⟨ a, ⟨ c, d ⟩ ⟩ => do
      let idents : Array Q(String) := #[a, c, d].map (.strVal · |> .lit)
      let ioPort := idents[0]!
      let outPort : Q(InternalPort String) :=
        q(InternalPort.mk (.internal $(idents[1]!)) $(idents[2]!))
      return q(($ioPort, $outPort))))
  let outputPorts : Q(List (String × InternalPort String)) ←
    mkListLit q(String × InternalPort String) (← outputConns.mapM (λ ⟨ ⟨ a, b ⟩, d ⟩ => do
      let idents : Array Q(String) := #[a, b, d].map (.strVal · |> .lit)
      let ioPort := idents[2]!
      let outPort : Q(InternalPort String) :=
        q(InternalPort.mk (.internal $(idents[0]!)) $(idents[1]!))
      return q(($ioPort, $outPort))))
  let modList : Q(List (String × String)) ←
    mkListLit (← mkAppM ``Prod #[mkConst ``String, mkConst ``String])
      (← instTypeMap.toList.mapM (fun (a, b) =>
        mkAppM ``Prod.mk #[.lit (.strVal a), .lit (.strVal b)]))
  let modListMap : Q(IdentMap String String) := q(List.toAssocList $modList)
  return q(ExprHigh.mk $modListMap (List.toAssocList $inputPorts)
                       (List.toAssocList $outputPorts) $connExpr)

open Lean.PrettyPrinter Delaborator SubExpr

namespace mergemod

def mergeHigh : ExprHigh String :=
  [graph|
    src0 [mod="io"];
    snk0 [mod="io"];

    fork1 [mod="fork"];
    fork2 [mod="fork"];
    merge1 [mod="merge"];
    merge2 [mod="merge"];

    src0 -> fork1 [inp="0"];

    fork1 -> fork2 [out="0",inp="0"];

    fork1 -> merge1 [out="1",inp="0"];
    fork2 -> merge1 [out="0",inp="1"];
    fork2 -> merge2 [out="1",inp="0"];

    merge1 -> merge2 [out="0",inp="1"];

    merge2 -> snk0 [out="0"];
  ]

#eval mergeHigh.lower.get rfl |>.higher


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
