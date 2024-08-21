import Leanses
import Lean
import Init.Data.BitVec.Lemmas
import Mathlib
import Qq

import DataflowRewriter.Simp
import DataflowRewriter.Module

open Qq

open Batteries (AssocList)
open Batteries (RBMap)

open Lean.Meta Lean.Elab

namespace DataflowRewriter

structure Connection where
  inputInstance  : Ident
  outputInstance : Ident
  inputPort      : Nat
  outputPort     : Nat
  deriving Repr, Hashable, DecidableEq, Ord

structure Interface where
  inputs : Nat
  outputs : Nat
  deriving Repr

structure IOPort where
  inPorts : List Nat
  outPorts : List Nat
  deriving Repr, Inhabited

structure ExprHigh where
  ioPorts     : List (Ident × IOPort)
  modules     : IdentMap Ident
  connections : List Connection
  deriving Repr

def Interface.ofModules (l : IdentMap ((T : Type _) × Module T)) : IdentMap Interface :=
  l.mapVal (λ _ (Sigma.mk _ m) => Interface.mk m.inputs.length m.outputs.length)

/-
Returns the maximum number of input and output ports for each module.
-/
-- def maxPorts (l : ExprHigh) : List (Nat × Nat) :=
--   Id.run <| do
--     let mut outL : List (Nat × Nat) := []
--     for mod in List.range (l.modules.length) do
--       let mut max_out := 0
--       let mut max_in := 0
--       for conn in l.connections do
--         match conn with
--         | .connect inputInstance outputInstance inputPort outputPort =>
--           if mod = inputInstance then max_in := max_in.max inputPort
--           if mod = outputInstance then max_out := max_out.max outputPort
--         | .dangleInput inst port => if mod = inst then max_in := max_in.max port
--         | .dangleOutput inst port => if mod = inst then max_out := max_out.max port-
--       outL := outL ++ [(max_in, max_out)]
--     return outL
def accumUntil (ports : IdentMap Interface) (n : Ident): Nat × Nat :=
  ports.foldl (λ a bi bo => if bi ≠ n then (a + (bo.inputs, bo.outputs)) else a) (0, 0)

def findInput (ports : IdentMap Interface) (n : Nat): Ident × Nat :=
  let (a, b, _) := ports.foldl (λ (a : Ident × Nat × Bool) bi bo =>
    let (_, a2, a3) := a
    if a2 + bo.inputs <= n && a3
    then (bi, a2 + bo.inputs, a3)
    else if a3 then (bi, n - a2, false) else a) ("", 0, true)
  (a, b)

def findOutput (ports : IdentMap Interface) (n : Nat): Ident × Nat :=
  let (a, b, _) := ports.foldl (λ (a : Ident × Nat × Bool) bi bo =>
    let (_, a2, a3) := a
    if a2 + bo.outputs <= n && a3
    then (bi, a2 + bo.outputs, a3)
    else if a3 then (bi, n - a2, false) else a) ("", 0, true)
  (a, b)

def connectWithOffset (ports : IdentMap Interface) (prod : ExprLow) (conn : Connection) : Option ExprLow := do
  let inputOffs := accumUntil ports conn.inputInstance
  let outputOffs := accumUntil ports conn.outputInstance
  let newProd := ExprLow.connect prod (inputOffs.fst + conn.inputPort) (outputOffs.snd + conn.outputPort)
  return newProd

def getEachInterface (i : IdentMap Interface) (e : ExprHigh) : Option (IdentMap Interface) :=
  e.modules.foldlM (λ nm k v => do nm.cons k (← i.find? v)) ∅

def lower (i : IdentMap Interface) (e : ExprHigh) : Option ExprLow := do
  let iomodules ← e.ioPorts.reverse.foldlM (λ a b => do
    let m ← e.modules.find? b.1
    return .cons b.1 m <| a.erase b.1
    ) e.modules
  match iomodules with
  | .cons m k ms =>
    let prod := (ms.toList.map (Function.uncurry ExprLow.base ·)).foldl ExprLow.product (ExprLow.base m k)
    e.connections.foldlM (connectWithOffset <| ← getEachInterface i e) prod
  | _ => none

protected def _root_.Batteries.AssocList.append : (xs ys : AssocList α β) → AssocList α β
  | .nil,    bs => bs
  | .cons a1 a2 as, bs => .cons a1 a2 <| as.append bs

instance : Append (AssocList α β) := ⟨AssocList.append⟩

def higher (i : IdentMap Interface) (e : ExprLow) : Option ExprHigh := do
  match e with
  | .base k n => pure ⟨ [], .cons k n .nil, [] ⟩
  | .product a b =>
    let ha ← higher i a
    let hb ← higher i b
    pure ⟨ [], ha.modules ++ hb.modules, ha.connections ++ hb.connections ⟩
  | .connect a ni no =>
    let ha ← higher i a
    let eachInt ← getEachInterface i ha
    let inp := findInput eachInt ni
    let out := findOutput eachInt no
    pure ⟨ [], ha.modules, ⟨ inp.1, out.1, inp.2, out.2 ⟩ :: ha.connections ⟩

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

open Term Lean.Syntax

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

open Lean in
@[term_elab dot_graph]
def dotGraphElab : TermElab := λ stx _typ? => do
  let mut idx := 0
  let mut hmap : HashMap Name String := mkHashMap
  let mut conns : List Connection := []
  for stmnt in stx[1][0].getArgs do
    let low_stmnt := stmnt.getArgs[0]!
    match low_stmnt with
    -- | `(dot_stmnt| $i:ident $[[$[$el:dot_attr],*]]? ) =>
    | `(dot_stmnt| $i:ident $[[$[$el:dot_attr],*]]? ) =>
      let some el := el
        | throwErrorAt i "No `mod` attribute found at node"
      let some modId ← findStxStr `mod el
        | throwErrorAt i "No `mod` attribute found at node"
      let (map', idx') := hmap.insertIfNew i.getId modId
      if idx'.isNone then
        hmap := map'; idx := idx + 1
      -- logInfo m!"{el.map (·.get! 1 |>.raw.getArgs.get! 0)}"
    | `(dot_stmnt| $a:ident -> $b:ident $[[$[$el:dot_attr],*]]? ) =>
      let mut out := 0
      let mut inp := 0
      if el.isSome then
        let el ← el
        out := (findStx `out el).getD 0
        inp := (findStx `inp el).getD 0
      -- logInfo m!"out = {out}, in = {inp}"
      conns := ⟨ b.getId.toString, a.getId.toString, inp, out ⟩ :: conns
    | _ => pure ()
  let lst := hmap.toList
  -- logInfo m!"{lst}"
  let connExpr : Q(List Connection) ← mkListLit (mkConst ``Connection) (← conns.mapM (λ ⟨ a, b, c, d ⟩ => do
    let idents := #[a, b].map (.strVal · |> .lit)
    let nats := #[c, d].map (.natVal · |> .lit)
    mkAppM ``Connection.mk (idents ++ nats)))
  let modList ← mkListLit (← mkAppM ``Prod #[mkConst ``Ident, mkConst ``Ident])
    (← lst.mapM (fun (a, b) => mkAppM ``Prod.mk #[.lit (.strVal a.toString), .lit (.strVal b)]))
  let modListMap : Q(IdentMap Ident) ← mkAppM ``List.toAssocList #[modList]
  let ioList : Q(List (Ident × IOPort)) := q([])
  return q(ExprHigh.mk $ioList $modListMap $connExpr)

open Lean.PrettyPrinter Delaborator SubExpr

-- @[delab app.DataflowRewriter.ExprHigh.mk]
-- def delabGraph : Delab := do
--   let nodes : TSyntaxArray `dot_stmnt ← withNaryArg 0 delab
--   let edges : TSyntaxArray `dot_stmnt ← withNaryArg 1 delab
--   let concat := nodes ++ edges
--   `([graph|
--       digraph {
--         $concat
--       }
--     ])

def merge3 : ExprHigh :=
  {[graph|
    merge1 [mod = "merge"];
    merge2 [mod = "merge"];
    merge1 -> merge2;
  ] with ioPorts := [ ("merge1", {(default : IOPort) with inPorts := [0, 1]})
                    , ("merge2", {inPorts := [1], outPorts := [0]})
                    ]}

#eval merge3

#eval lower [ ("merge", ⟨ 2, 1 ⟩) ].toAssocList merge3

def highlow int mod := do
  higher int <| ← lower int mod

#eval highlow [ ("merge", ⟨ 2, 1 ⟩) ].toAssocList merge3

namespace mergemod

def inPort (i : Ident) : Ident × IOPort :=
  (i, {inPorts := [0], outPorts := []})

def outPort (i : Ident) : Ident × IOPort :=
  (i, {inPorts := [], outPorts := [0]})

@[simp]
def mergeHigh : ExprHigh :=
  {[graph|
    src0 [mod="io"];
    snk0 [mod="io"];

    fork1 [mod="fork"];
    fork2 [mod="fork"];
    merge1 [mod="merge"];
    merge2 [mod="merge"];

    src0 -> fork1;

    fork1 -> fork2 [out=1];

    fork1 -> merge1;
    fork2 -> merge1 [inp=1];
    fork2 -> merge2 [out=1,inp=1];

    merge1 -> merge2;

    merge2 -> snk0;
  ] with ioPorts := [inPort "src0", outPort "snk0"]}

def _root_.Batteries.AssocList.filterKeys (p : α → Bool) : AssocList α β → AssocList α β
  | .nil => .nil
  | .cons a b as => match p a with
    | true => .cons a b <| as.filterKeys p
    | false => as.filterKeys p

def fromConnection (l : List Connection) (instances : List Ident): List (Ident × IOPort) :=
  l.foldl (λ lcon conn =>
    if conn.inputInstance ∈ instances
    then if lcon.any (·.1 == conn.inputInstance)
         then lcon.replaceF λ a => if a.1 == conn.inputInstance then some (a.1, {a.2 with inPorts := a.2.inPorts ++ [conn.inputPort]}) else none
         else lcon ++ [(conn.inputInstance, {inPorts := [conn.inputPort], outPorts := []})]
    else if lcon.any (·.1 == conn.outputInstance)
         then lcon.replaceF λ a => if a.1 == conn.outputInstance then some (a.1, {a.2 with outPorts := a.2.outPorts ++ [conn.outputPort]}) else none
         else lcon ++ [(conn.outputInstance, {outPorts := [conn.outputPort], inPorts := []})]) []

def appendIOPort (a b : IOPort) : IOPort :=
  { inPorts := a.inPorts ++ b.inPorts, outPorts := a.outPorts ++ b.outPorts }

def mergeLists (l1 l2 : List (Ident × IOPort)) : List (Ident × IOPort) :=
  (RBMap.ofList l1 compare).mergeWith (λ _ => appendIOPort) (RBMap.ofList l2 compare) |>.toList

def sortIOPort' (a : IOPort) : IOPort :=
  { inPorts := a.inPorts.mergeSort (r := (· ≤ ·)), outPorts := a.outPorts.mergeSort (r := (· ≤ ·)) }

def sortIOPort (a : List (Ident × IOPort)) : List (Ident × IOPort) :=
  a.map λ (a, b) => (a, sortIOPort' b)

def _root_.DataflowRewriter.ExprHigh.subgraph (e : ExprHigh) (instances : List Ident) : ExprHigh :=
  let new_modules := e.modules.filterKeys (· ∈ instances)
  let new_connections := e.connections.filter λ a => a.inputInstance ∈ instances && a.outputInstance ∈ instances
  let generated_io := (e.connections.filter λ a =>
    a.inputInstance ∈ instances || a.outputInstance ∈ instances).removeAll new_connections
  let new_io_ports := e.ioPorts.filter λ s => s.1 ∈ instances
  { ioPorts := fromConnection generated_io instances |> mergeLists new_io_ports |> sortIOPort,
    modules := new_modules,
    connections := new_connections }

def _root_.DataflowRewriter.ExprHigh.replaceInst
    (e : ExprHigh)
    (ports : IdentMap Interface)
    (instances : List Ident)
    (inst : Ident)
    (mod : Ident)
    : ExprHigh :=
  let new_modules := e.modules.filterKeys (· ∉ instances) |> (AssocList.cons inst mod ·)
  let new_conns :=
    e.connections.foldl (λ conns curr =>
      -- First, skip the internal connections
      if curr.inputInstance ∈ instances && curr.outputInstance ∈ instances then conns
      else
        if curr.inputInstance ∈ instances then
          -- Instance in the input, the input needs to be reconnected to the
          -- input of the new instance.
          let inputOffs := accumUntil ports curr.inputInstance
          conns.concat <| Connection.mk inst curr.outputInstance (inputOffs.fst + curr.inputPort) curr.outputPort
        else if curr.outputInstance ∈ instances then
               -- Instance in the input, the input needs to be reconnected to the
               -- input of the new instance.
               let outputOffs := accumUntil ports curr.outputInstance
               conns.concat <| Connection.mk curr.inputInstance inst curr.inputPort (outputOffs.snd + curr.outputPort)
             else conns.concat curr
    ) []
  let new_io :=
    e.ioPorts.foldl (λ conns curr =>
      if curr.fst ∉ instances then conns.concat curr
      else
        let offs := accumUntil ports curr.fst
        let new_io := IOPort.mk (curr.snd.inPorts.map (· + offs.fst)) (curr.snd.outPorts.map (· + offs.snd))
        conns.concat (inst, new_io)
    ) []
  { ioPorts := new_io,
    modules := new_modules,
    connections := new_conns }

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

def _root_.DataflowRewriter.ExprHigh.shatter_io : Unit := sorry

def _root_.DataflowRewriter.ExprHigh.connect_io (e: ExprHigh): ExprHigh := sorry

end mergemod

end DataflowRewriter
