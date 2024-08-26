import Leanses
import Lean
import Init.Data.BitVec.Lemmas
import Mathlib
import Qq

import DataflowRewriter.Simp
import DataflowRewriter.List

open Qq

open Batteries (AssocList)
open Batteries (RBMap)

open Lean.Meta Lean.Elab

namespace DataflowRewriter

abbrev Ident := String
deriving instance BEq for Ident

deriving instance Repr for Ident
deriving instance Hashable for Ident
deriving instance DecidableEq for Ident
deriving instance Ord for Ident

deriving instance Repr for AssocList

abbrev IdentMap α := AssocList Ident α

inductive ExprLow where
  | base : Ident → Ident → ExprLow
  | product : ExprLow → ExprLow → ExprLow
  | connect : ExprLow → Nat → Nat → ExprLow
  deriving Repr

structure Module (S : Type u₁) : Type (max u₁ 1) where
  inputs : List ((T : Type 0) × (S → T → S → Prop))
  outputs : List ((T : Type 0) × (S → T → S → Prop))
  internals : List (S → S → Prop)

mklenses Module
open Module.l

def empty : Module S := {inputs := [], outputs := [], internals:= []}

@[simp]
def getIO.{u₁, u₂} {S : Type u₁} (l: List ((T : Type u₂) × (S → T → S → Prop))) (n : Nat): ((T : Type u₂) × (S → T → S → Prop)) :=
  l.getD n (⟨ PUnit, λ _ _ _ => True ⟩)

@[simp]
def getRule {S : Type _} (l : List (S → S → Prop)) (n : Nat) : (S → S → Prop) :=
  l.getD n (λ _ _ => True)

variable (baseModules : Fin n → ((T : Type) × Module T))

structure matching_interface (imod : Module I) (smod : Module S) : Prop where
  input_types : ∀ (ident : Fin imod.inputs.length), (imod.inputs.get ident).1 = (getIO smod.inputs ident).1
  output_types : ∀ (ident : Fin imod.outputs.length), (imod.outputs.get ident).1 = (getIO smod.outputs ident).1

section Trace

variable {S : Type _}
variable (mod : Module S)

inductive existSR : S → S → Prop where
  | done : ∀ init, existSR init init
  | step :
    ∀ init mid final n,
      (getRule mod.internals n) init mid →
      existSR mid final →
      existSR init final

end Trace

section Refinement

variable {I : Type _}
variable {S : Type _}
variable (imod : Module I)
variable (smod : Module S)

variable (matching : matching_interface imod smod)

/--
This could be made even more flexible by passing a custom type comparison
function for the inputs and outputs.  For now this might be general enough
though.
-/
structure indistinguishable (init_i : I) (init_s : S) : Prop where
  inputs_indistinguishable : ∀ (ident : Fin imod.inputs.length)
  new_i v,
    (imod.inputs.get ident).2 init_i v new_i →
    ∃ new_s, (getIO smod.inputs ident).2 init_s ((matching.input_types ident).mp v) new_s
  outputs_indistinguishable : ∀ ident new_i v,
    (imod.outputs.get ident).2 init_i v new_i →
    ∃ new_s, (getIO smod.outputs ident).2 init_s ((matching.output_types ident).mp v) new_s

structure comp_refines (R : I → S → Prop) (init_i : I) (init_s : S) : Prop where
  inputs :
    ∀ (ident : Fin imod.inputs.length) mid_i v,
      (imod.inputs.get ident).2 init_i v mid_i →
      ∃ almost_mid_s mid_s,
        (getIO smod.inputs ident).2 init_s ((matching.input_types ident).mp v) almost_mid_s
        ∧ existSR smod almost_mid_s mid_s
        ∧ R mid_i mid_s
        ∧ indistinguishable imod smod matching mid_i mid_s
  outputs :
    ∀ (ident : Fin imod.outputs.length) mid_i v,
      (imod.outputs.get ident).2 init_i v mid_i →
      ∃ almost_mid_s mid_s,
        (getIO smod.outputs ident).2 init_s ((matching.output_types ident).mp v) almost_mid_s
        ∧ existSR smod almost_mid_s mid_s
        ∧ R mid_i mid_s
        ∧ indistinguishable imod smod matching mid_i mid_s
  internals :
    ∀ (ident : Fin imod.internals.length) mid_i,
      (getRule imod.internals ident) init_i mid_i →
      ∃ mid_s,
        existSR smod init_s mid_s
        ∧ R mid_i mid_s
        ∧ indistinguishable imod smod matching mid_i mid_s

def refines (R : I → S → Prop) :=
  ∀ (init_i : I) (init_s : S),
    R init_i init_s →
    indistinguishable imod smod matching init_i init_s →
    comp_refines imod smod matching R init_i init_s

end Refinement

section Semantics

def connect (mod : Module S) (i : Fin mod.inputs.length) (o : Fin mod.outputs.length)
      (wf : (mod.inputs.get i).1 = (mod.outputs.get o).1) : Module S :=
       { inputs := mod.inputs.remove i,
         outputs :=  mod.outputs.remove o,
         internals :=  (λ st st' => ∃ consumed_output output, (mod.outputs.get o).2 st output consumed_output ∧
                              (mod.inputs.get i).2 consumed_output (Eq.rec id wf output) st')
                        :: mod.internals }

/--
`connect'` will produce a new rule that fuses an input with an output, with a
precondition that the input and output type must match.
-/
@[simp]
def connect' (mod : Module S) (i : Fin mod.inputs.length) (o : Fin mod.outputs.length) : Module S :=
       { inputs := mod.inputs.remove i ,
         outputs :=  mod.outputs.remove o,
         internals :=  (λ st st' => ∀ wf : (mod.inputs.get i).1 = (mod.outputs.get o).1,
                            ∃ consumed_output output, (mod.outputs.get o).2 st output consumed_output ∧
                              (mod.inputs.get i).2 consumed_output (Eq.rec id wf output) st')
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
      { inputs := mod1.inputs.map liftL ++ mod2.inputs.map liftR,
        outputs := mod1.outputs.map liftL ++ mod2.outputs.map liftR,
        internals := mod1.internals.map liftL' ++ mod2.internals.map liftR'
      }

@[simp]
def build_module' (e : ExprLow) (ε : IdentMap ((T: Type _) × Module T))
  : Option ((T: Type _) × Module T) :=
  match e with
  | .base _ e => ε.find? e
  | .connect e' i o => do
    let e ← build_module' e' ε
    if hi : i < e.2.inputs.length then
      if ho : o < e.2.outputs.length then
        let i := ⟨i, hi⟩;
        let o := ⟨o, ho⟩;
        return ⟨e.1, connect' e.2 i o⟩
    .none
  | .product a b => do
    let a <- build_module' a ε;
    let b <- build_module' b ε;
    return ⟨a.1 × b.1, product a.2 b.2⟩

end Semantics

section GraphSyntax

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

def _root_.DataflowRewriter.ExprHigh.subgraph_inst (e : ExprHigh) (instances : List Ident) (inst : Ident) : ExprHigh :=
  let new_modules := e.modules.filterKeys (· ∉ instances)
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
          -- Instance in the input; the input needs to be reconnected to the
          -- input of the new instance.
          let inputOffs := accumUntil ports curr.inputInstance
          conns.concat <| Connection.mk inst curr.outputInstance (inputOffs.fst + curr.inputPort) curr.outputPort
        else if curr.outputInstance ∈ instances then
               -- Instance in the output; the output needs to be reconnected to the
               -- output of the new instance.
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

def _root_.DataflowRewriter.ExprHigh.shatter_io : Unit := sorry

def _root_.DataflowRewriter.ExprHigh.connect_io (e: ExprHigh): ExprHigh := sorry

end mergemod

end GraphSyntax

section RefinementTheorem

end RefinementTheorem

end DataflowRewriter
