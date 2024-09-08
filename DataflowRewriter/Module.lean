import Leanses
import Lean
import Init.Data.BitVec.Lemmas
import Mathlib
import Qq

import DataflowRewriter.Simp
import DataflowRewriter.List

open Qq

open Batteries (AssocList)

open Batteries (RBMap RBSet)

open Lean.Meta Lean.Elab

namespace DataflowRewriter

abbrev Ident := String
deriving instance BEq for Ident

deriving instance Repr for Ident
deriving instance Hashable for Ident
deriving instance DecidableEq for Ident
deriving instance Ord for Ident

deriving instance Repr for AssocList

abbrev IdentMap α := RBMap Ident α compare
abbrev IdentSet := RBSet Ident compare

structure InternalPort where
  inst : Ident
  name : Ident
deriving Repr, Hashable, DecidableEq, Ord, Inhabited

instance : ToString InternalPort where
  toString
    | ⟨ a, b ⟩ => a ++ "." ++ b

inductive ExprLow where
  | base : Ident → Ident → ExprLow
  | rename : InternalPort → Ident → ExprLow → ExprLow
  | product : ExprLow → ExprLow → ExprLow
  | connect : InternalPort → InternalPort → ExprLow → ExprLow
  deriving Repr

structure Module (S : Type u₁) : Type (max u₁ 1) where
  inputs : IdentMap ((T : Type 0) × (S → T → S → Prop))
  outputs : IdentMap ((T : Type 0) × (S → T → S → Prop))
  internals : List (S → S → Prop)

mklenses Module
open Module.l

def empty : Module S := {inputs := ∅, outputs := ∅, internals:= []}

@[simp]
def IdentMap.getIO.{u₁, u₂} {S : Type u₁} (l: IdentMap ((T : Type u₂) × (S → T → S → Prop))) (n : Ident): ((T : Type u₂) × (S → T → S → Prop)) :=
  l.findD n (⟨ PUnit, λ _ _ _ => True ⟩)

@[simp]
def _root_.List.getRule {S : Type _} (l : List (S → S → Prop)) (n : Nat) : (S → S → Prop) :=
  l.getD n (λ _ _ => True)

-- variable (baseModules : Fin n → ((T : Type) × Module T))

structure matching_interface (imod : Module I) (smod : Module S) : Prop where
  input_types : ∀ (ident : Ident), (imod.inputs.getIO ident).1 = (smod.inputs.getIO ident).1
  output_types : ∀ (ident : Ident), (imod.outputs.getIO ident).1 = (smod.outputs.getIO ident).1

section Trace

variable {S : Type _}

inductive existSR (mod : Module S) : S → S → Prop where
  | done : ∀ init, existSR mod init init
  | step :
    ∀ init mid final n,
      (mod.internals.getRule n) init mid →
      existSR mod mid final →
      existSR mod init final

end Trace

class MatchingModules (I : Type _) (S : Type _) where
  imod : Module I
  smod : Module S
  matching : matching_interface imod smod

section Refinement

variable {I : Type _}
variable {S : Type _}

variable [mm : MatchingModules I S]

/--
This could be made even more flexible by passing a custom type comparison
function for the inputs and outputs.  For now this might be general enough
though.
-/
structure indistinguishable (init_i : I) (init_s : S) : Prop where
  inputs_indistinguishable : ∀ (ident : Ident)
  new_i v,
    (mm.imod.inputs.getIO ident).2 init_i v new_i →
    ∃ new_s, (mm.smod.inputs.getIO ident).2 init_s ((mm.matching.input_types ident).mp v) new_s
  outputs_indistinguishable : ∀ ident new_i v,
    (mm.imod.outputs.getIO ident).2 init_i v new_i →
    ∃ new_s, (mm.smod.outputs.getIO ident).2 init_s ((mm.matching.output_types ident).mp v) new_s

structure comp_refines (R : I → S → Prop) (init_i : I) (init_s : S) : Prop where
  inputs :
    ∀ (ident : Ident) mid_i v,
      (mm.imod.inputs.getIO ident).2 init_i v mid_i →
      ∃ almost_mid_s mid_s,
        (mm.smod.inputs.getIO ident).2 init_s ((mm.matching.input_types ident).mp v) almost_mid_s
        ∧ existSR mm.smod almost_mid_s mid_s
        ∧ R mid_i mid_s
        ∧ indistinguishable mid_i mid_s
  outputs :
    ∀ (ident : Ident) mid_i v,
      (mm.imod.outputs.getIO ident).2 init_i v mid_i →
      ∃ almost_mid_s mid_s,
        (mm.smod.outputs.getIO ident).2 init_s ((mm.matching.output_types ident).mp v) almost_mid_s
        ∧ existSR mm.smod almost_mid_s mid_s
        ∧ R mid_i mid_s
        ∧ indistinguishable mid_i mid_s
  internals :
    ∀ (ident : Nat) mid_i,
      (mm.imod.internals.getRule ident) init_i mid_i →
      ∃ mid_s,
        existSR mm.smod init_s mid_s
        ∧ R mid_i mid_s
        ∧ indistinguishable mid_i mid_s

def refines (R : I → S → Prop) :=
  ∀ (init_i : I) (init_s : S),
    R init_i init_s →
    indistinguishable init_i init_s →
    comp_refines R init_i init_s

end Refinement

section Semantics

def connect (mod : Module S) (i o : Ident)
      (wf : (mod.inputs.getIO i).1 = (mod.outputs.getIO o).1) : Module S :=
       { inputs := mod.inputs.erase i,
         outputs :=  mod.outputs.erase o,
         internals :=  (λ st st' => ∃ consumed_output output, (mod.outputs.getIO o).2 st output consumed_output ∧
                              (mod.inputs.getIO i).2 consumed_output (Eq.rec id wf output) st')
                        :: mod.internals }

/--
`connect'` will produce a new rule that fuses an input with an output, with a
precondition that the input and output type must match.
-/
@[simp]
def connect' (mod : Module S) (o i : Ident) : Module S :=
       { inputs := mod.inputs.erase i ,
         outputs :=  mod.outputs.erase o,
         internals :=  (λ st st' => ∀ wf : (mod.inputs.getIO i).1 = (mod.outputs.getIO o).1,
                            ∃ consumed_output output, (mod.outputs.getIO o).2 st output consumed_output ∧
                              (mod.inputs.getIO i).2 consumed_output (Eq.rec id wf output) st')
                              :: mod.internals }

@[simp]
def liftL (x: (T : Type _) × (S → T → S → Prop)) : (T : Type _) × (S × S' → T → S × S' → Prop) :=
      ⟨ x.1, λ (a,b) ret (a',b') => x.2 a ret a' ∧ b = b' ⟩

@[simp]
def liftR (x: (T : Type _) × (S' → T → S' → Prop)) : (T : Type _) × (S × S' → T → S × S' → Prop) :=
      ⟨ x.1, λ (a,b) ret (a',b') => x.2 b ret b' ∧ a = a' ⟩

@[simp]
def liftL' (x:  S → S → Prop) : S × S' → S × S' → Prop :=
      λ (a,b) (a',b') => x a a' ∧ b = b'

@[simp]
def liftR' (x:  S' → S' → Prop) : S × S' → S × S' → Prop :=
      λ (a,b) (a',b') => x b b' ∧ a = a'

@[simp]
def product (mod1 : Module S) (mod2: Module S') : Module (S × S') :=
      { inputs := (mod1.inputs.mapVal (λ _ => liftL)).mergeWith (λ _ a _ => a) (mod2.inputs.mapVal (λ _ => liftR)),
        outputs := (mod1.outputs.mapVal (λ _ => liftL)).mergeWith (λ _ a _ => a) (mod2.outputs.mapVal (λ _ => liftR)),
        internals := mod1.internals.map liftL' ++ mod2.internals.map liftR'
      }

def _root_.Batteries.RBMap.modifyKeys (map : RBMap α β c) (f : α → α) : RBMap α β c :=
  map.foldl (λ new_map k v => new_map.insert (f k) v) ∅

def Module.renamePorts (mod : Module S) (f : Ident → Ident) : Module S :=
  { inputs := mod.inputs.modifyKeys f,
    outputs := mod.outputs.modifyKeys f,
    internals := mod.internals
  }

@[simp]
def build_module' (e : ExprLow) (ε : IdentMap ((T: Type _) × Module T))
  : Option ((T: Type _) × Module T) := do
  match e with
  | .base i e =>
    let mod ← ε.find? e
    return ⟨ mod.1, mod.2.renamePorts (i ++ "." ++ ·) ⟩
  | .rename a b e' =>
    let e ← build_module' e' ε
    return ⟨ e.1, e.2.renamePorts (λ a' => if a' == toString a then b else a') ⟩
  | .connect o i e' =>
    let e ← build_module' e' ε
    return ⟨e.1, connect' e.2 (toString o) (toString i)⟩
  | .product a b =>
    let a <- build_module' a ε;
    let b <- build_module' b ε;
    return ⟨a.1 × b.1, product a.2 b.2⟩

end Semantics

section GraphSyntax

structure Connection where
  output : InternalPort
  input  : InternalPort
  deriving Repr, Hashable, DecidableEq, Ord, Inhabited

structure ExprHigh where
  modules     : IdentMap Ident
  inPorts     : IdentMap InternalPort
  outPorts    : IdentMap InternalPort
  connections : List Connection

instance : Repr ExprHigh where
  reprPrec a _ := 
    let instances := a.modules.foldl (λ s inst mod => s ++ s!"\n {inst} [mod = \"{mod}\"];") ""
    let inPorts := a.inPorts.foldl (λ s i port => s ++ s!"\n {i} -> {port.inst} [inp = \"{port.name}\"];") ""
    let outPorts := a.outPorts.foldl (λ s i port => s ++ s!"\n {port.inst} -> {i} [out = \"{port.name}\"];") ""
    let connections := a.connections.foldl (λ s => λ | ⟨ oport, iport ⟩ => s ++ s!"\n {oport.inst} -> {iport.inst} [out = \"{oport.name}\", in = \"{iport.name}\"];") ""
    s!"[graph| {instances} {inPorts} {outPorts} {connections}\n ]"

def lower (e : ExprHigh) : Option ExprLow :=
  match e.modules.toList with
  | x :: xs =>
    let prod_expr := xs.foldl (fun expr val => .product (.base val.1 val.2) expr) (.base x.1 x.2)
    let conn_expr := e.connections.foldl (fun expr conn => .connect conn.output conn.input expr) prod_expr
    let in_ports_conn := e.inPorts.foldl (fun expr i port => .rename port i expr) conn_expr
    some <| e.outPorts.foldl (fun expr i port => .rename port i expr) in_ports_conn
  | _ => none

def merge3 : ExprHigh :=
  { modules := RBMap.ofList [("merge_inst", "merge")] _
  , inPorts := RBMap.ofList [("a", ⟨ "merge_inst", "a"⟩), ("b", ⟨ "merge_inst", "b"⟩)] _
  , outPorts := RBMap.ofList [("c", ⟨ "merge_inst", "c"⟩)] _
  , connections := []
  }

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
      let some el := el
        | throwErrorAt (mkListNode #[a, b]) "No `mod` attribute found at node"
      let mut out ← (findStxStr `out el) -- | throwErrorAt (mkListNode el) "No input found"
      let mut inp ← (findStxStr `inp el) -- | throwErrorAt (mkListNode el) "No output found"
      if out.isNone && hmap[a.getId] == "io" then out := some a.getId.toString
      if inp.isNone && hmap[b.getId] == "io" then inp := some b.getId.toString
      let some out' := out | throwErrorAt (mkListNode el) "No output found"
      let some inp' := inp | throwErrorAt (mkListNode el) "No input found"
      -- logInfo m!"out = {out}, in = {inp}"
      conns := ⟨ ⟨ a.getId.toString, out' ⟩, ⟨ b.getId.toString, inp' ⟩ ⟩ :: conns
    | _ => pure ()
  let lst := hmap.toList
  -- logInfo m!"{lst}"
  let internalConns := conns.filter (fun | ⟨x, y⟩ => hmap[x.inst.toName] != "io" && hmap[y.inst.toName] != "io")
  let inputConns := conns.filter (fun | ⟨x, _⟩ => hmap[x.inst.toName] == "io")
  let outputConns := conns.filter (fun | ⟨_, y⟩ => hmap[y.inst.toName] == "io")
  let connExpr : Q(List Connection) ← mkListLit (mkConst ``Connection) (← internalConns.mapM (λ ⟨ ⟨ a, b ⟩, ⟨ c, d ⟩ ⟩ => do
    let idents : Array Q(String) := #[a, b, c, d].map (.strVal · |> .lit)
    let inPort : Q(InternalPort) := q(InternalPort.mk $(idents[0]!) $(idents[1]!))
    let outPort : Q(InternalPort) := q(InternalPort.mk $(idents[2]!) $(idents[3]!))
    mkAppM ``Connection.mk #[inPort, outPort]))
  let inputPorts : Q(List (Ident × InternalPort)) ← mkListLit q(Ident × InternalPort) (← inputConns.mapM (λ ⟨ ⟨ a, b ⟩, ⟨ c, d ⟩ ⟩ => do
    let idents : Array Q(String) := #[a, b, c, d].map (.strVal · |> .lit)
    let ioPort := idents[1]!
    let outPort : Q(InternalPort) := q(InternalPort.mk $(idents[2]!) $(idents[3]!))
    return q(($ioPort, $outPort))))
  let outputPorts : Q(List (Ident × InternalPort)) ← mkListLit q(Ident × InternalPort) (← outputConns.mapM (λ ⟨ ⟨ a, b ⟩, ⟨ c, d ⟩ ⟩ => do
    let idents : Array Q(String) := #[a, b, c, d].map (.strVal · |> .lit)
    let ioPort := idents[3]!
    let outPort : Q(InternalPort) := q(InternalPort.mk $(idents[0]!) $(idents[1]!))
    return q(($ioPort, $outPort))))
  let modList : Q(List (Ident × Ident)) ← mkListLit (← mkAppM ``Prod #[mkConst ``Ident, mkConst ``Ident])
    (← lst.mapM (fun (a, b) => mkAppM ``Prod.mk #[.lit (.strVal a.toString), .lit (.strVal b)]))
  let modListMap : Q(IdentMap Ident) := q(Batteries.RBMap.ofList $modList compare)
  return q(ExprHigh.mk $modListMap (Batteries.RBMap.ofList $inputPorts compare) 
                       (Batteries.RBMap.ofList $outputPorts compare) $connExpr)

open Lean.PrettyPrinter Delaborator SubExpr

namespace mergemod

@[simp]
def mergeHigh : ExprHigh :=
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

def compareProd (i j : Ident × Ident) := 
  match compare i.1 j.1 with
  | .eq => compare i.2 j.2
  | a => a

def _root_.DataflowRewriter.ExprHigh.subgraph (e : ExprHigh) (instances : List Ident) 
    (newInputs newOutputs : IdentMap InternalPort) : ExprHigh :=
  { inPorts := e.inPorts.filter (λ _ b => b.inst ∈ instances) |>.mergeWith (λ _ a _ => a) newInputs,
    outPorts := e.outPorts.filter (λ _ b => b.inst ∈ instances) |>.mergeWith (λ _ a _ => a) newOutputs,
    modules := e.modules.filter (λ b _ => b ∈ instances),
    connections := e.connections.filter λ a => a.input.inst ∈ instances && a.output.inst ∈ instances }

def _root_.DataflowRewriter.ExprHigh.subgraph' (e : ExprHigh) (instances : List Ident) 
    (newInputs newOutputs : IdentMap InternalPort) : ExprHigh :=
  e.subgraph (e.modules.keysList.diff instances) 
    (newOutputs.mapVal λ _ v => ((e.connections.find? λ | ⟨ o, _ ⟩ => v = o).getD default).input) 
    (newInputs.mapVal λ _ v => ((e.connections.find? λ | ⟨ _, i ⟩ => v = i).getD default).output)

def _root_.DataflowRewriter.ExprHigh.subgraph'' (e : ExprHigh) (instances : List Ident) 
    (newInputs newOutputs : IdentMap InternalPort) : ExprHigh :=
  e.subgraph (e.modules.keysList.diff instances) newInputs newOutputs

def mergeHighSubgraph := mergeHigh.subgraph ["merge1"] (RBMap.ofList [("merge1_a", ⟨"merge1", "inp1"⟩), ("merge1_b", ⟨"merge1", "inp2"⟩)] _)
  (RBMap.ofList [("merge1_c", ⟨"merge1", "out"⟩)] _)

def mergeHighSubgraph' := mergeHigh.subgraph' ["merge1"] (RBMap.ofList [("merge1_a", ⟨"merge1", "inp1"⟩), ("merge1_b", ⟨"merge1", "inp2"⟩)] _)
  (RBMap.ofList [("merge1_c", ⟨"merge1", "out"⟩)] _)

open Lean Meta PrettyPrinter Delaborator SubExpr in
elab "#delab" e:term : command => do
  let l ← Command.liftTermElabM do
    instantiateMVars <| (← Term.elabTerm e none)
  logInfo (repr l)

#eval mergeHighSubgraph
#check ({ modules := RBMap.ofList [("merge1", "merge")] _,
          inPorts := RBMap.ofList [("merge1_a", { inst := "merge1", name := "inp1" }),
                      ("merge1_b", { inst := "merge1", name := "inp2" })] _,
          outPorts := RBMap.ofList [("merge1_c", { inst := "merge1", name := "out" })] _,
          connections := [] } : ExprHigh)
#eval mergeHighSubgraph'
#check ({ modules := RBMap.ofList [("fork1", "fork"), ("fork2", "fork"), ("merge2", "merge"), ("snk0", "io"), ("src0", "io")] _,
          inPorts := RBMap.ofList [("merge1_c", { inst := "merge2", name := "inp2" }),
                      ("src0", { inst := "fork1", name := "inp" })] _,
          outPorts := RBMap.ofList [("merge1_a", { inst := "fork1", name := "out2" }),
                       ("merge1_b", { inst := "fork2", name := "out1" }),
                       ("snk0", { inst := "merge2", name := "out" })] _,
          connections := [{ output := { inst := "fork2", name := "out2" }, input := { inst := "merge2", name := "inp1" } },
                  { output := { inst := "fork1", name := "out1" }, input := { inst := "fork2", name := "inp" } }] } : ExprHigh)

def _root_.DataflowRewriter.ExprHigh.inline (e e' : ExprHigh) : Option ExprHigh := do
  let new_input_connections ← e'.inPorts.foldlM (λ conns i port => do 
                                                    let outP ← e.outPorts.find? i
                                                    return Connection.mk port outP :: conns) []
  let new_output_connections ← e'.outPorts.foldlM (λ conns i port => do 
                                                    let inpP ← e.inPorts.find? i
                                                    return Connection.mk inpP port :: conns) []
  return { inPorts := e.inPorts.filter (λ a _ => a ∉ e'.outPorts.keysList),
           outPorts := e.outPorts.filter (λ a _ => a ∉ e'.inPorts.keysList),
           modules := e.modules.mergeWith (λ _ a _ => a) e'.modules,
           connections := e.connections
                          ++ new_input_connections
                          ++ new_output_connections
                          ++ e'.connections
         }

#eval mergeHigh
#check ({ modules := RBMap.ofList [("fork1", "fork"),
              ("fork2", "fork"),
              ("merge1", "merge"),
              ("merge2", "merge"),
              ("snk0", "io"),
              ("src0", "io")] _,
           inPorts := RBMap.ofList [("snk0", { inst := "merge2", name := "out" })] _,
           outPorts := RBMap.ofList [("src0", { inst := "fork1", name := "inp" })] _,
           connections := [{ input := { inst := "merge2", name := "inp2" }, output := { inst := "merge1", name := "out" } },
                  { input := { inst := "merge2", name := "inp1" }, output := { inst := "fork2", name := "out2" } },
                  { input := { inst := "merge1", name := "inp2" }, output := { inst := "fork2", name := "out1" } },
                  { input := { inst := "merge1", name := "inp1" }, output := { inst := "fork1", name := "out2" } },
                  { input := { inst := "fork2", name := "inp" }, output := { inst := "fork1", name := "out1" } }] } : ExprHigh)

#eval mergeHighSubgraph'.inline mergeHighSubgraph
#check ({ modules := RBMap.ofList [("fork1", "fork"),
              ("fork2", "fork"),
              ("merge1", "merge"),
              ("merge2", "merge"),
              ("snk0", "io"),
              ("src0", "io")] _,
          inPorts := RBMap.ofList [("snk0", { inst := "merge2", name := "out" })] _,
          outPorts := RBMap.ofList [("src0", { inst := "fork1", name := "inp" })] _,
          connections := [{ input := { inst := "merge2", name := "inp1" }, output := { inst := "fork2", name := "out2" } },
                  { input := { inst := "fork2", name := "inp" }, output := { inst := "fork1", name := "out1" } },
                  { input := { inst := "merge1", name := "inp2" }, output := { inst := "fork2", name := "out1" } },
                  { input := { inst := "merge1", name := "inp1" }, output := { inst := "fork1", name := "out2" } },
                  { input := { inst := "merge2", name := "inp2" }, output := { inst := "merge1", name := "out" } }] } : ExprHigh)

end mergemod

end GraphSyntax

section RefinementTheorem

end RefinementTheorem

end DataflowRewriter
