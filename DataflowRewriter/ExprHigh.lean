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

@[drunfold] def lower' (el : ExprLow Ident) (e : ExprHigh Ident) : ExprLow Ident :=
  let prod_expr :=
    e.modules.toList.foldl (λ expr val =>
        -- return .product (.base (int.toPortMapping val.1) val.2) expr)
        .product (Function.uncurry .base val.snd) expr) el
  e.connections.foldl (λ expr conn => .connect conn.output conn.input expr) prod_expr

@[drunfold] def lower (e : ExprHigh Ident) : Option (ExprLow Ident) :=
  match e.modules.toList with
  | x :: xs => some <| {e with modules := xs.toAssocList}.lower' (Function.uncurry .base x.snd)
  | _ => none

end ExprHigh

class FreshIdent (Ident : Type _) where
  next : Nat → Ident

instance : FreshIdent String where
  next n := "mod" ++ toString n

instance : FreshIdent Nat where
  next := id

namespace ExprLow

variable {Ident : Type _}
variable [DecidableEq Ident]
variable [Inhabited Ident]

def higher' [FreshIdent Ident] (fresh : Nat) : ExprLow Ident → (ExprHigh Ident × Nat)
| .base a b =>
  (ExprHigh.mk [(a.ofPortMapping.getD (FreshIdent.next fresh), (a, b))].toAssocList ∅, fresh + 1)
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

namespace ExprHigh

variable {Ident : Type _}
variable [DecidableEq Ident]
variable [Inhabited Ident]

@[drunfold] def reorder (g : ExprHigh Ident) (sub : List Ident) : ExprHigh Ident :=
  let m1 := g.modules.filter (λ k v => k ∈ sub)
  let m2 := g.modules.filter (λ k v => k ∉ sub)
  {g with modules := m1 ++ m2}

@[drunfold] def extract (g : ExprHigh Ident) (sub : List Ident) : ExprHigh Ident :=
  ⟨ g.modules.filter (λ k v => k ∈ sub)
  , g.connections.filter (λ | ⟨o, i⟩ => o.inst.elem sub && i.inst.elem sub)
  ⟩

@[drunfold] def rest (g : ExprHigh Ident) (sub : List Ident) : ExprHigh Ident :=
  ⟨ g.modules.filter (λ k v => k ∉ sub)
  , g.connections.filter (λ | ⟨o, i⟩ => !(o.inst.elem sub && i.inst.elem sub))
  ⟩

@[drunfold] def replace [FreshIdent Ident]
  (g : ExprHigh Ident) (sub : List Ident) (g' : ExprHigh Ident)
  : Option (ExprHigh Ident) := do
  let e_sub ← g.extract sub |>.lower
  let g_lower := g.rest sub |>.lower' e_sub
  let g'_lower ← g'.lower
  g_lower.replace e_sub g'_lower |>.higher

@[drunfold]
def rename [FreshIdent Ident]
    (typ : Ident) (p : PortMapping Ident) (g : ExprHigh Ident) : Option (ExprHigh Ident) := do
  let g_lower ← g.lower
  g_lower.rename typ p |>.higher

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

end ExprHigh

namespace Module

variable {Ident : Type _}

def liftGraph {S} (m : Module Ident S) (p : PortMapping Ident) (inst typ : Ident) : ExprHigh Ident :=
  { modules := [(inst, p, typ)].toAssocList
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

#check true

open Lean in
def findStxBool (n : Name) (stx : Array Syntax) : Option Bool := do
  let mut out := none
  for pair in stx do
    if pair[0].getId = n then
      out := match pair[2] with
             | `(dot_value| true) => .some true
             | `(dot_value| false) => .some false
             | _ => .none
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

def parseInternalPort (s : String) : Option (InternalPort String) :=
  match s.splitOn "." with
  | [single] => some ⟨.top, single⟩
  | [first, second] => some ⟨.internal first, second⟩
  | _ => none

open Lean Qq in
def reifyInternalPort : InternalPort String → Q(InternalPort String)
| ⟨ .top, s ⟩ =>
  let s' : Q(String) := .lit (.strVal s)
  q(InternalPort.mk .top $s')
| ⟨ .internal a, b ⟩ =>
  let a' : Q(String) := .lit (.strVal a)
  let b' : Q(String) := .lit (.strVal b)
  q(InternalPort.mk (.internal $a') $b')

open Lean Qq in
def reifyInternalPort' {u : Level} {α : Q(Type $u)} : InternalPort Q($α) → Q(InternalPort $α)
| ⟨ .top, s ⟩ => q(InternalPort.mk .top $s)
| ⟨ .internal a, b ⟩ => q(InternalPort.mk (.internal $a) $b)

-- open Lean Qq in
-- def reifyPortMapping (p : PortMapping String) : Q(PortMapping String) :=
--   q(@PortMapping.mk String )

def updatePortMappingInput (s : Std.HashMap String (PortMapping String × String))
  (inCluster : Bool)
  (inPort : InternalPort String)
  : Bool → InternalPort String → Std.HashMap String (PortMapping String × String)
| _, co@⟨.top, n⟩ =>
  match (inCluster, inPort) with
  | (true, ci@⟨.internal x, y⟩) =>
    let (a, b) := s[x]!
    s.insert x ({a with output := a.output.cons ci co}, b)
  | (false, ⟨.internal x, y⟩) =>
    let (a, b) := s[x]!
    s.insert x ({a with output := a.output.cons ⟨.top, y⟩ co}, b)
  | _ => s
| false, c@⟨.internal i, x⟩ =>
  let (a, b) := s[i]!
  s.insert i ({a with input := a.input.cons ⟨.top, x⟩ c}, b)
| true, ⟨.internal _, _⟩ => s

def updatePortMappingOutput (s : Std.HashMap String (PortMapping String × String))
  (inCluster : Bool)
  (inPort : InternalPort String)
  : Bool → InternalPort String → Std.HashMap String (PortMapping String × String)
| _, co@⟨.top, n⟩ =>
  match (inCluster, inPort) with
  | (true, ci@⟨.internal x, y⟩) =>
    let (a, b) := s[x]!
    s.insert x ({a with input := a.input.cons ci co}, b)
  | (false, ⟨.internal x, y⟩) =>
    let (a, b) := s[x]!
    s.insert x ({a with input := a.input.cons ⟨.top, y⟩ co}, b)
  | _ => s
| false, c@⟨.internal i, x⟩ =>
  let (a, b) := s[i]!
  s.insert i ({a with output := a.output.cons ⟨.top, x⟩ c}, b)
| true, ⟨.internal _, _⟩ => s

open Lean Qq in
def mkAssocListExpr {u : Level} {α β : Q(Type $u)}
  : Batteries.AssocList Q($α) Q($β) → Q(Batteries.AssocList $α $β)
| .cons a b r => let r' := mkAssocListExpr r; q(.cons $a $b $r')
| .nil => q(.nil)

open Lean Qq in
def mkPortMapping {u : Level} {α : Q(Type $u)} : PortMapping Q($α) → Q(PortMapping $α)
| ⟨ a, b ⟩ =>
  let a' := a.mapKey reifyInternalPort' |>.mapVal (λ _ => reifyInternalPort') |> mkAssocListExpr
  let b' := b.mapKey reifyInternalPort' |>.mapVal (λ _ => reifyInternalPort') |> mkAssocListExpr
  q(@PortMapping.mk $α $a' $b')

open Lean Qq in
@[term_elab dot_graph]
def dotGraphElab : TermElab := λ stx _typ? => do
  let mut instMap : Std.HashMap Name (InstIdent String × Bool) := ∅
  let mut instTypeMap : Std.HashMap String (PortMapping String × String) := ∅
  let mut conns : List (Connection String) := []
  for stmnt in stx[1][0].getArgs do
    let low_stmnt := stmnt.getArgs[0]!
    match low_stmnt with
    | `(dot_stmnt| $i:ident $[[$[$el:dot_attr],*]]? ) =>
      let some el := el
        | throwErrorAt i "No `mod` attribute found at node"
      let some modId ← findStxStr `mod el
        | throwErrorAt i "No `mod` attribute found at node"
      let mut modInst : InstIdent String := .top
      let mut modCluster : Bool := findStxBool `cluster el |>.getD false
      unless modId == "io" do
        modInst := .internal i.getId.toString
      let (b, map') := instMap.containsThenInsertIfNew i.getId (modInst, modCluster)
      if !b then
        instMap := map'
        -- IO "modules" are not added to the instTypeMap.
        unless modId == "io" do instTypeMap := instTypeMap.insert i.getId.toString (∅, modId)
      else
        logWarning s!"Multiple references to {i.getId} found"
    | `(dot_stmnt| $a:ident -> $b:ident $[[$[$el:dot_attr],*]]? ) =>
      -- Error checking to report it early if the instance is not present in the
      -- hashmap.
      let some aInst := instMap[a.getId]? | throwErrorAt a "Instance has not been declared"
      let some bInst := instMap[b.getId]? | throwErrorAt b "Instance has not been declared"
      if aInst.fst = .top && bInst.fst = .top then
        throwErrorAt a "Both the input and output are IO ports"
      let some el := el
        | throwErrorAt (mkListNode #[a, b]) "No `mod` attribute found at node"
      let mut out ← (findStxStr `out el)
      let mut inp ← (findStxStr `inp el)
      -- If no port name is provided and the port is a top-level port, then use
      -- the instance name as the port name.
      if out.isNone && aInst.fst.isTop then out := some a.getId.toString
      if inp.isNone && bInst.fst.isTop then inp := some b.getId.toString
      let some out' := out | throwErrorAt (mkListNode el) "No output found"
      let some inp' := inp | throwErrorAt (mkListNode el) "No input found"
      let some outPort := parseInternalPort out'
        | throwErrorAt (mkListNode el) "Output port format incorrect"
      let some inPort := parseInternalPort inp'
        | throwErrorAt (mkListNode el) "Input port format incorrect"
      -- If the instance is a cluster do not modify the name, otherwise as the
      -- instance as a prefix.
      let outPort' := if aInst.snd then outPort else ⟨aInst.fst, outPort.name⟩
      let inPort' := if bInst.snd then inPort else ⟨bInst.fst, inPort.name⟩
      -- If one of the end points is an external port then do not add a
      -- connection into the graph.
      unless aInst.fst = .top || bInst.fst = .top do
        conns := ⟨ outPort', inPort' ⟩ :: conns
        instTypeMap := updatePortMappingOutput instTypeMap bInst.snd inPort' aInst.snd outPort'
        instTypeMap := updatePortMappingInput instTypeMap aInst.snd outPort' bInst.snd inPort'
      if aInst.fst = .top then
        instTypeMap := updatePortMappingOutput instTypeMap bInst.snd inPort' aInst.snd outPort'
      if bInst.fst = .top then
        instTypeMap := updatePortMappingInput instTypeMap aInst.snd outPort' bInst.snd inPort'
    | _ => pure ()
  let connExpr : Q(List (Connection String)) ←
    mkListLit q(Connection String) (← conns.mapM (λ ⟨ a, b ⟩ => do
      mkAppM ``Connection.mk #[reifyInternalPort a, reifyInternalPort b]))
  let modList : Q(List (String × (PortMapping String × String))) ←
    mkListLit q(String × (PortMapping String × String))
      (instTypeMap.toList.map (fun (a, (p, b)) =>
        let a' : Q(String) := .lit (.strVal a)
        let b' : Q(String) := .lit (.strVal b)
        let p' : Q(PortMapping String) := mkPortMapping <| p.map (.strVal · |> .lit)
        q(($a', ($p', $b')))))
  let modListMap : Q(IdentMap String (PortMapping String × String)) := q(List.toAssocList $modList)
  return q(ExprHigh.mk $modListMap $connExpr)

-- open Lean.PrettyPrinter Delaborator SubExpr

-- namespace mergemod

def mergeHigh : ExprHigh String :=
  [graph|
    src0 [mod="src"];
    snk0 [mod="snk"];

    fork1 [mod="fork"];
    fork2 [mod="fork"];
    merge1 [mod="merge"];
    merge2 [mod="merge"];

    src0 -> fork1 [out="0",inp="0"];

    fork1 -> fork2 [out="0",inp="0"];

    fork1 -> merge1 [out="1",inp="0"];
    fork2 -> merge1 [out="0",inp="1"];
    fork2 -> merge2 [out="1",inp="0"];

    merge1 -> merge2 [out="0",inp="1"];

    merge2 -> snk0 [out="0",inp="0"];
  ]


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




end DataflowRewriter
