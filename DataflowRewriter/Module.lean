/-
Copyright (c) 2024 Yann Herklotz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Leanses
import Lean
import Init.Data.BitVec.Lemmas
import Qq

import DataflowRewriter.Simp
import DataflowRewriter.List

open Qq

open Batteries (AssocList)

open Batteries (RBMap RBSet)

open Lean.Meta Lean.Elab

deriving instance Repr for AssocList

namespace DataflowRewriter

structure Wr (T : Type _) where
  unwrap : T
deriving Repr, Inhabited, Hashable, DecidableEq, Ord, BEq

-- abbrev Ident := Nat

-- deriving instance BEq for Ident
-- deriving instance Repr for Ident
-- deriving instance Hashable for Ident
-- deriving instance DecidableEq for Ident
-- deriving instance Ord for Ident

section Module

variable (Ident : Type _)

structure InternalPort where
  inst : Ident
  name : Ident
  deriving Repr, Hashable, DecidableEq, Ord, Inhabited, BEq

instance [Inhabited Ident] : Coe Ident (InternalPort Ident) where
  coe a := ⟨default, a⟩

abbrev PortMap α := AssocList (InternalPort Ident) α
abbrev IdentMap α := AssocList Ident α
abbrev IdentSet := Finset Ident

-- instance : Coe Ident InternalPort where
--   coe i := ⟨0, i⟩

-- instance (n : Nat) : OfNat InternalPort n where
--   ofNat := ⟨ 0, n ⟩

-- def internalPortToString : InternalPort → String
--   | ⟨ a, b ⟩ => a ++ "." ++ b

inductive ExprLow where
  | base : Ident → Ident → ExprLow
  | input : InternalPort Ident → Ident → ExprLow → ExprLow
  | output : InternalPort Ident → Ident → ExprLow → ExprLow
  | product : ExprLow → ExprLow → ExprLow
  | connect : InternalPort Ident → InternalPort Ident → ExprLow → ExprLow
  deriving Repr

structure Module.{u₁} (S : Type u₁) where
  inputs : PortMap Ident ((T : Type) × (S → T → S → Prop))
  outputs : PortMap Ident ((T : Type) × (S → T → S → Prop))
  internals : List (S → S → Prop)

-- mklenses Module
-- open Module.l

-- abbrev Module' S := Wr (Module S)

variable {Ident}
variable [BEq Ident]
variable [Inhabited Ident]

def Module.empty {S} : Module Ident S := {inputs := ∅, outputs := ∅, internals:= ∅}

-- def Module'.empty {S} : Module' S := Wr.mk {inputs := ∅, outputs := ∅, internals:= ∅}

@[simp]
def PortMap.getIO.{u₁, u₂} {S : Type u₁} (l: PortMap Ident (Σ (T : Type u₂), (S → T → S → Prop))) (n : Ident): (Σ (T : Type u₂), (S → T → S → Prop)) :=
  (l.find? ↑n).getD (⟨ PUnit, λ _ _ _ => True ⟩)

@[simp]
def PortMap.getInternalPort.{u₁, u₂} {S : Type u₁} (l: PortMap Ident (Σ (T : Type u₂), (S → T → S → Prop))) (n : InternalPort Ident): (Σ (T : Type u₂), (S → T → S → Prop)) :=
  (l.find? n).getD (⟨ PUnit, λ _ _ _ => True ⟩)

-- @[simp]
-- def _root_.Finset.getRule {S : Type _} (l : Finset (S → S → Prop)) (n : Nat) : (S → S → Prop) :=
--   l.lookup n (λ _ _ => True)

-- variable (baseModules : Fin n → ((T : Type) × Module T))

structure matching_interface {I S} (imod : Module Ident I) (smod : Module Ident S) : Prop where
  input_keys : ∀ (ident : Ident), imod.inputs.contains ↑ident → smod.inputs.contains ↑ident
  output_keys : ∀ (ident : Ident), imod.outputs.contains ↑ident → smod.outputs.contains ↑ident
  input_types : ∀ (ident : Ident), (imod.inputs.getIO ident).1 = (smod.inputs.getIO ident).1
  output_types : ∀ (ident : Ident), (imod.outputs.getIO ident).1 = (smod.outputs.getIO ident).1

section Trace

variable {S : Type _}

inductive existSR (mod : Module Ident S) : S → S → Prop where
  | done : ∀ init, existSR mod init init
  | step :
    ∀ init mid final rule,
      rule ∈ mod.internals →
      rule init mid →
      existSR mod mid final →
      existSR mod init final

end Trace

end Module

class MatchingModules (I : Type _) (S : Type _) (Ident : outParam (Type _)) [BEq Ident] [Inhabited Ident] where
  imod : Module Ident I
  smod : Module Ident S
  matching : matching_interface imod smod

section Refinement

variable {I : Type _}
variable {S : Type _}
variable {Ident : Type _}
variable [BEq Ident]
variable [Inhabited Ident]

variable [mm : MatchingModules I S Ident]

/--
This could be made even more flexible by passing a custom type comparison
function for the inputs and outputs.  For now this might be general enough
though.
-/
structure indistinguishable (init_i : I) (init_s : S) : Prop where
  inputs_indistinguishable : ∀ (ident : Ident) new_i v,
    mm.imod.inputs.contains ↑ident →
    (mm.imod.inputs.getIO ident).2 init_i v new_i →
    ∃ new_s, (mm.smod.inputs.getIO ident).2 init_s ((mm.matching.input_types ident).mp v) new_s
  outputs_indistinguishable : ∀ ident new_i v,
    mm.imod.outputs.contains ↑ident →
    (mm.imod.outputs.getIO ident).2 init_i v new_i →
    ∃ new_s, (mm.smod.outputs.getIO ident).2 init_s ((mm.matching.output_types ident).mp v) new_s

structure comp_refines (R : I → S → Prop) (init_i : I) (init_s : S) : Prop where
  inputs :
    ∀ ident mid_i v,
      mm.imod.inputs.contains ↑ident →
      (mm.imod.inputs.getIO ident).2 init_i v mid_i →
      ∃ almost_mid_s mid_s,
        (mm.smod.inputs.getIO ident).2 init_s ((mm.matching.input_types ident).mp v) almost_mid_s
        ∧ existSR mm.smod almost_mid_s mid_s
        ∧ R mid_i mid_s
        ∧ indistinguishable mid_i mid_s
  outputs :
    ∀ ident mid_i v,
      mm.imod.outputs.contains ↑ident →
      (mm.imod.outputs.getIO ident).2 init_i v mid_i →
      ∃ almost_mid_s mid_s,
        (mm.smod.outputs.getIO ident).2 init_s ((mm.matching.output_types ident).mp v) almost_mid_s
        ∧ existSR mm.smod almost_mid_s mid_s
        ∧ R mid_i mid_s
        ∧ indistinguishable mid_i mid_s
  internals :
    ∀ rule mid_i,
      rule ∈ mm.imod.internals →
      rule init_i mid_i →
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

variable {Ident : Type _}
variable [BEq Ident]
variable [Inhabited Ident]

/--
`connect'` will produce a new rule that fuses an input with an output, with a
precondition that the input and output type must match.
-/
@[simp]
def connect' {S : Type _} (mod : Module Ident S) (o i : InternalPort Ident) : Module Ident S :=
       { inputs := mod.inputs.erase i ,
         outputs :=  mod.outputs.erase o,
         internals :=  (λ st st' => ∀ wf : (mod.inputs.getInternalPort i).1 = (mod.outputs.getInternalPort o).1,
                            ∃ consumed_output output, (mod.outputs.getInternalPort o).2 st output consumed_output ∧
                              (mod.inputs.getInternalPort i).2 consumed_output (Eq.rec id wf output) st')
                              :: mod.internals }

@[simp]
def liftL {S S'} (x: (T : Type _) × (S → T → S → Prop)) : (T : Type _) × (S × S' → T → S × S' → Prop) :=
      ⟨ x.1, λ (a,b) ret (a',b') => x.2 a ret a' ∧ b = b' ⟩

@[simp]
def liftR {S S'} (x: (T : Type _) × (S' → T → S' → Prop)) : (T : Type _) × (S × S' → T → S × S' → Prop) :=
      ⟨ x.1, λ (a,b) ret (a',b') => x.2 b ret b' ∧ a = a' ⟩

@[simp]
def liftL' {S S'} (x:  S → S → Prop) : S × S' → S × S' → Prop :=
      λ (a,b) (a',b') => x a a' ∧ b = b'

@[simp]
def liftR' {S S'} (x:  S' → S' → Prop) : S × S' → S × S' → Prop :=
      λ (a,b) (a',b') => x b b' ∧ a = a'

def _root_.Batteries.AssocList.append {α β} (a b : AssocList α β) : AssocList α β :=
  match a with
  | .nil => b
  | .cons x y xs => 
    .cons x y <| xs.append b

@[simp]
def product {S S'} (mod1 : Module Ident S) (mod2: Module Ident S') : Module Ident (S × S') :=
      { inputs := (mod1.inputs.mapVal (λ _ => liftL)).append (mod2.inputs.mapVal (λ _ => liftR)),
        outputs := (mod1.outputs.mapVal (λ _ => liftL)).append (mod2.outputs.mapVal (λ _ => liftR)),
        internals := mod1.internals.map liftL' ++ mod2.internals.map liftR'
      }

def _root_.Batteries.RBMap.modifyKeys {α β c} (map : RBMap α β c) (f : α → α) : RBMap α β c :=
  map.foldl (λ new_map k v => new_map.insert (f k) v) ∅

def _root_.Batteries.AssocList.modifyKeys {α β} (map : AssocList α β) (f : α → α) : AssocList α β :=
  map.foldl (λ new_map k v => new_map.cons (f k) v) ∅

def _root_.Batteries.AssocList.keysList {α β} (map : AssocList α β) : List α :=
  map.toList.map (·.fst)

def Module.renamePorts {S} (mod : Module Ident S) (f : InternalPort Ident → InternalPort Ident) : Module Ident S :=
  { inputs := mod.inputs.modifyKeys f,
    outputs := mod.outputs.modifyKeys f,
    internals := mod.internals
  }

def Module.renameToInput {S} (mod : Module Ident S) (f : InternalPort Ident → InternalPort Ident) : Module Ident S :=
  { inputs := mod.inputs.modifyKeys f,
    outputs := mod.outputs,
    internals := mod.internals
  }

def Module.renameToOutput {S} (mod : Module Ident S) (f : InternalPort Ident → InternalPort Ident) : Module Ident S :=
  { inputs := mod.inputs,
    outputs := mod.outputs.modifyKeys f,
    internals := mod.internals
  }

@[simp]
def build_module' (e : ExprLow Ident) (ε : IdentMap Ident ((T: Type _) × Module Ident T))
  : Option ((T: Type _) × Module Ident T) := do
  match e with
  | .base i e =>
    let mod ← ε.find? e
    return ⟨ mod.1, mod.2.renamePorts (λ ⟨ _, y ⟩ => ⟨ i, y ⟩ ) ⟩
  | .input a b e' =>
    let e ← build_module' e' ε
    return ⟨ e.1, e.2.renameToInput (λ p => if p == a then ↑b else p) ⟩
  | .output a b e' =>
    let e ← build_module' e' ε
    return ⟨ e.1, e.2.renameToOutput (λ p => if p == a then ↑b else p) ⟩
  | .connect o i e' =>
    let e ← build_module' e' ε
    return ⟨e.1, connect' e.2 o i⟩
  | .product a b =>
    let a <- build_module' a ε;
    let b <- build_module' b ε;
    return ⟨a.1 × b.1, product a.2 b.2⟩

def build_module (e : ExprLow Ident) (map : IdentMap Ident ((T : Type _) × Module Ident T)) (h : (build_module' e map).isSome = true := by decide):  (T : Type _) × Module Ident T :=
  (build_module' e map).get h

end Semantics

section GraphSyntax

variable (Ident : Type _)
variable [Repr Ident]

structure Connection where
  output : InternalPort Ident
  input  : InternalPort Ident
  deriving Repr, Hashable, DecidableEq, Ord, Inhabited

structure ExprHigh where
  modules     : IdentMap Ident Ident
  inPorts     : IdentMap Ident (InternalPort Ident)
  outPorts    : IdentMap Ident (InternalPort Ident)
  connections : List (Connection Ident)

instance : Repr (ExprHigh Ident) where
  reprPrec a _ :=
    let instances := a.modules.foldl (λ s inst mod => s ++ s!"\n {repr inst} [mod = \"{repr mod}\"];") ""
    let inPorts := a.inPorts.foldl (λ s i port => s ++ s!"\n {repr i} -> {repr port.inst} [inp = \"{repr port.name}\"];") ""
    let outPorts := a.outPorts.foldl (λ s i port => s ++ s!"\n {repr port.inst} -> {repr i} [out = \"{repr port.name}\"];") ""
    let connections := a.connections.foldl (λ s => λ | ⟨ oport, iport ⟩ => s ++ s!"\n {repr oport.inst} -> {repr iport.inst} [out = \"{repr oport.name}\", in = \"{repr iport.name}\"];") ""
    s!"[graph| {instances} {inPorts} {outPorts} {connections}\n ]"

variable {Ident}

def lower (e : ExprHigh Ident) : Option (ExprLow Ident) :=
  match e.modules.toList with
  | x :: xs =>
    let prod_expr := xs.foldl (fun expr val => .product (.base val.1 val.2) expr) (.base x.1 x.2)
    let conn_expr := e.connections.foldl (fun expr conn => .connect conn.output conn.input expr) prod_expr
    let in_ports_conn := e.inPorts.foldl (fun expr i port => .input port i expr) conn_expr
    some <| e.outPorts.foldl (fun expr i port => .output port i expr) in_ports_conn
  | _ => none

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
  let mut idx := 1
  let mut idx' := 0
  let mut hmap : Std.HashMap Name String := ∅
  let mut instMap : Std.HashMap Name Nat := ∅
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
      let (b, map') := hmap.containsThenInsertIfNew i.getId modId
      if !b then
        hmap := map'
        instMap := instMap.insert i.getId idx
        revInstMap := revInstMap.insert idx i.getId
        idx := idx + 1
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
      conns := ⟨ ⟨ instMap[a.getId]!, out' ⟩, ⟨ instMap[b.getId]!, inp' ⟩ ⟩ :: conns
    | _ => pure ()
  let lst := hmap.toList
  -- logInfo m!"{lst}"
  let internalConns := conns.filter (fun | ⟨x, y⟩ => hmap[revInstMap[x.inst]!]! != "io" && hmap[revInstMap[y.inst]!]! != "io")
  let inputConns := conns.filter (fun | ⟨x, _⟩ => hmap[revInstMap[x.inst]!]! == "io")
  let outputConns := conns.filter (fun | ⟨_, y⟩ => hmap[revInstMap[y.inst]!]! == "io")
  let connExpr : Q(List (Connection Nat)) ← mkListLit q(Connection Nat) (← internalConns.mapM (λ ⟨ ⟨ a, b ⟩, ⟨ c, d ⟩ ⟩ => do
    let idents : Array Q(Nat) := #[a, b, c, d].map (.natVal · |> .lit)
    let inPort : Q(InternalPort Nat) := q(InternalPort.mk $(idents[0]!) $(idents[1]!))
    let outPort : Q(InternalPort Nat) := q(InternalPort.mk $(idents[2]!) $(idents[3]!))
    mkAppM ``Connection.mk #[inPort, outPort]))
  let inputPorts : Q(List (Nat × InternalPort Nat)) ← mkListLit q(Nat × InternalPort Nat) (← inputConns.mapM (λ ⟨ ⟨ a, b ⟩, ⟨ c, d ⟩ ⟩ => do
    let idents : Array Q(Nat) := #[a, b, c, d].map (.natVal · |> .lit)
    let ioPort := idents[1]!
    let outPort : Q(InternalPort Nat) := q(InternalPort.mk $(idents[2]!) $(idents[3]!))
    return q(($ioPort, $outPort))))
  let outputPorts : Q(List (Nat × InternalPort Nat)) ← mkListLit q(Nat × InternalPort Nat) (← outputConns.mapM (λ ⟨ ⟨ a, b ⟩, ⟨ c, d ⟩ ⟩ => do
    let idents : Array Q(Nat) := #[a, b, c, d].map (.natVal · |> .lit)
    let ioPort := idents[3]!
    let outPort : Q(InternalPort Nat) := q(InternalPort.mk $(idents[0]!) $(idents[1]!))
    return q(($ioPort, $outPort))))
  let modList : Q(List (Nat × Nat)) ← mkListLit (← mkAppM ``Prod #[mkConst ``Nat, mkConst ``Nat])
    (← lst.mapM (fun (a, b) => mkAppM ``Prod.mk #[.lit (.natVal instMap[a]!), .lit (.natVal modMap[b]!)]))
  let modListMap : Q(IdentMap Nat Nat) := q(List.toAssocList $modList)
  return q(ExprHigh.mk $modListMap (List.toAssocList $inputPorts)
                       (List.toAssocList $outputPorts) $connExpr)

open Lean.PrettyPrinter Delaborator SubExpr

namespace mergemod

@[simp]
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

-- def compareProd (i j : Ident × Ident) :=
--   match compare i.1 j.1 with
--   | .eq => compare i.2 j.2
--   | a => a

def _root_.Batteries.AssocList.filter {α β} (f : α → β → Bool) (l : AssocList α β) :=
  l.foldl (λ c a b => if f a b then c.cons a b else c) (∅ : AssocList α β)

-- variable [BEq Ident]
variable [DecidableEq Ident]
variable [Inhabited Ident]

def _root_.DataflowRewriter.ExprHigh.subgraph (e : ExprHigh Ident) (instances : List Ident)
    (newInputs newOutputs : IdentMap Ident (InternalPort Ident)) : ExprHigh Ident :=
  { inPorts := (e.inPorts.filter (λ _ b => b.inst ∈ instances)).append newInputs,
    outPorts := (e.outPorts.filter (λ _ b => b.inst ∈ instances)).append newOutputs,
    modules := e.modules.filter (λ b _ => b ∈ instances),
    connections := e.connections.filter λ a => a.input.inst ∈ instances && a.output.inst ∈ instances }

def _root_.DataflowRewriter.ExprHigh.subgraph' (e : ExprHigh Ident) (instances : List Ident)
    (newInputs newOutputs : IdentMap Ident (InternalPort Ident)) : ExprHigh Ident :=
  e.subgraph (e.modules.keysList.diff instances)
    (newOutputs.mapVal λ _ v => ((e.connections.find? λ | ⟨ o, _ ⟩ => v = o).getD default).input)
    (newInputs.mapVal λ _ v => ((e.connections.find? λ | ⟨ _, i ⟩ => v = i).getD default).output)

def _root_.DataflowRewriter.ExprHigh.subgraph'' (e : ExprHigh Ident) (instances : List Ident)
    (newInputs newOutputs : IdentMap Ident (InternalPort Ident)) : ExprHigh Ident :=
  e.subgraph (e.modules.keysList.diff instances) newInputs newOutputs

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

def _root_.DataflowRewriter.ExprHigh.inline (e e' : ExprHigh Ident) : Option (ExprHigh Ident) := do
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

end GraphSyntax

section NModule

instance {n} : OfNat (InternalPort Nat) n where
  ofNat := ⟨ 0, n ⟩

abbrev NModule := Module Nat

end NModule

end DataflowRewriter
