import Lean
import Qq

import DataflowRewriter.ExprHigh

namespace DataflowRewriter

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
        | throwErrorAt pair[2][0] "`type` attribute is not a string"
      out := some out'
  return out

def toInstIdent {α} [Inhabited α] (n : String) (h : Std.HashMap String α) : InstIdent α :=
  match n with
  | "io" => .top
  | s => .internal h[s]!

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
  let mut instMap : Std.HashMap String (InstIdent String × Bool) := ∅
  let mut instTypeMap : Std.HashMap String (PortMapping String × String) := ∅
  let mut conns : List (Connection String) := []
  for stmnt in stx[1][0].getArgs do
    let low_stmnt := stmnt.getArgs[0]!
    match low_stmnt with
    | `(dot_stmnt| $i:ident $[[$[$el:dot_attr],*]]? ) =>
      let some el := el
        | throwErrorAt i "No `type` attribute found at node"
      let some modId ← findStxStr `type el
        | throwErrorAt i "No `type` attribute found at node"
      let mut modCluster : Bool := findStxBool `cluster el |>.getD false
      match updateNodeMaps ⟨instMap, instTypeMap⟩ i.getId.toString modId modCluster with
      | .ok ⟨a, b⟩ =>
        instMap := a
        instTypeMap := b
      | .error s =>
        throwErrorAt i s
    | `(dot_stmnt| $a:ident -> $b:ident $[[$[$el:dot_attr],*]]? ) =>
      -- Error checking to report it early if the instance is not present in the
      -- hashmap.
      let some el := el
        | throwErrorAt (mkListNode #[a, b]) "No `type` attribute found at node"
      let mut out ← (findStxStr `out el)
      let mut inp ← (findStxStr `inp el)
      match updateConnMaps ⟨instMap, instTypeMap⟩ conns a.getId.toString b.getId.toString out inp with
      | .ok (⟨_, b⟩, c) =>
        conns := c
        instTypeMap := b
      | .error (.outInstError s) => throwErrorAt a s
      | .error (.inInstError s) => throwErrorAt b s
      | .error (.portError s) => throwErrorAt (mkListNode el) s
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

-- def mergeHigh : ExprHigh String :=
--   [graph|
--     src0 [mod="src"];
--     snk0 [mod="snk"];

--     fork1 [mod="fork"];
--     fork2 [mod="fork"];
--     merge1 [mod="merge"];
--     merge2 [mod="merge"];

--     src0 -> fork1 [out="0",inp="0"];

--     fork1 -> fork2 [out="0",inp="0"];

--     fork1 -> merge1 [out="1",inp="0"];
--     fork2 -> merge1 [out="0",inp="1"];
--     fork2 -> merge2 [out="1",inp="0"];

--     merge1 -> merge2 [out="0",inp="1"];

--     merge2 -> snk0 [out="0",inp="0"];
--   ]

end DataflowRewriter
