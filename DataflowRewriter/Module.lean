import Leanses
import Lean
import Init.Data.BitVec.Lemmas
import Mathlib
import DataflowRewriter.Reduce
import DataflowRewriter.Simp
import Qq

open Qq

open Batteries (AssocList)
open Batteries (RBMap)

open Lean.Meta Lean.Elab
namespace DataflowRewriter

structure Module (S : Type u₁) : Type (max u₁ 1) where
  inputs : List ((T : Type 0) × (S -> T -> S -> Prop))
  outputs : List ((T : Type 0) × (S -> T -> S -> Prop))
  internals : List (S -> S -> Prop)

mklenses Module
open Module.l

def empty : Module S := {inputs := [], outputs := [], internals:= []}

@[simp]
def _root_.List.remove {α : Type u} (as : List α) (i : Fin as.length) : List α := as.eraseIdx i

def connect (mod : Module S) (i : Fin mod.inputs.length) (o : Fin mod.outputs.length)
      (wf : (mod.inputs.get i).1 = (mod.outputs.get o).1) : Module S :=
       { inputs := mod.inputs.remove i,
         outputs :=  mod.outputs.remove o,
         internals :=  (λ st st' => ∃ consumed_output output, (mod.outputs.get o).2 st output consumed_output ∧
                              (mod.inputs.get i).2 consumed_output (Eq.rec id wf output) st')
                        :: mod.internals }

-- @[simp]
-- def source (l : List ((T : Type) × T)) : Module (Fin l.length → ((T : Type) × List T)) :=
--   { inputs := ((List.drange l.length).zip l).map 
--               (λ (n, (Sigma.mk T d)) => ⟨ T, λ s t s' => s' = update_Fin n ⟩),
--     internals := [],
--     outputs := l.map (λ (Sigma.mk T d) => ⟨ T, λ _ t _ => t = d ⟩)
--   }

@[simp]
def io (T : Type) : Module (List T) :=
  { inputs := [⟨ T, λ s t s' => s' = t :: s ⟩],
    internals := [],
    outputs := [⟨ T, λ s t s' => s = s' ++ [t] ⟩]
  }

@[simp]
def sink (l : List Type) : Module Unit :=
  { inputs := l.map (λ T => ⟨ T, λ _ _ _ => True ⟩),
    internals := [],
    outputs := []
  }

@[simp]
def connect' (mod : Module S) (i : Fin mod.inputs.length) (o : Fin mod.outputs.length) : Module S :=
       { inputs := mod.inputs.remove i ,
         outputs :=  mod.outputs.remove o,
         internals :=  (λ st st' => ∀ wf : (mod.inputs.get i).1 = (mod.outputs.get o).1,
                            ∃ consumed_output output, (mod.outputs.get o).2 st output consumed_output ∧
                              (mod.inputs.get i).2 consumed_output (Eq.rec id wf output) st')
                              :: mod.internals }

@[simp]
def liftL (x: (T : Type _) × (S -> T -> S -> Prop)) : (T : Type _) × (S × S' -> T -> S × S' -> Prop) :=
      ⟨ x.1, λ (a,b) ret (a',b') => x.2 a ret a' ∧ b = b' ⟩

@[simp]
def liftR (x: (T : Type _) × (S' -> T -> S' -> Prop)) : (T : Type _) × (S × S' -> T -> S × S' -> Prop) :=
      ⟨ x.1, λ (a,b) ret (a',b') => x.2 b ret b' ∧ a = a' ⟩

@[simp]
def liftL' (x:  S -> S -> Prop) : S × S' -> S × S' -> Prop :=
      λ (a,b) (a',b') => x a a' ∧ b = b'

@[simp]
def liftR' (x:  S' -> S' -> Prop) : S × S' -> S × S' -> Prop :=
      λ (a,b) (a',b') => x b b' ∧ a = a'

@[simp]
def product (mod1 : Module S) (mod2: Module S') : Module (S × S') :=
      { inputs := mod1.inputs.map liftL ++ mod2.inputs.map liftR,
        outputs := mod1.outputs.map liftL ++ mod2.outputs.map liftR,
        internals := mod1.internals.map liftL' ++ mod2.internals.map liftR'
      }
@[simp]
def merge_inputs (mod : Module S) (in1 in2 : Fin (List.length mod.inputs)) : Module S  :=
      { inputs :=
        let in1_t := mod.inputs.get in1;
        let in2_t := mod.inputs.get in2;
        let rmin2 := List.remove mod.inputs in2;
        List.set rmin2 in2.1 ⟨ in1_t.1 × in2_t.1, λ s (v1,v2) s' =>
              ∃ s_int, in1_t.2 s v1 s_int ∧
              in2_t.2 s_int v2 s'⟩
      ,
        outputs := mod.outputs,
        internals := mod.internals }
@[simp]
def merge_outputs (mod : Module S) (out1 out2 : Fin (List.length mod.outputs)) : Module S  :=
      { outputs :=
        let out1_t := mod.outputs.get out1;
        let out2_t := mod.outputs.get out2;
        let rmout2 := List.remove mod.outputs out2;
        List.set rmout2 out2.1 ⟨ out1_t.1 × out2_t.1, λ s (v1,v2) s' =>
              ∃ s_int, out1_t.2 s v1 s_int ∧
              out2_t.2 s_int v2 s'⟩
      ,
        inputs := mod.inputs,
        internals := mod.internals }

@[simp]
def merge T : Module (List T):=
      { inputs := [⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩,
                   ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩],
        outputs := [⟨ T, λ oldList oldElement newList => ∃ i, newList = oldList.remove i ∧ oldElement = oldList.get i ⟩],
        internals := []
      }

@[simp]
def fork T : Module (List T):=
      { inputs := [⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩],
        outputs := [ ⟨ T, λ oldList oldElement newList => ∃ i, newList = oldList.remove i ∧ oldElement = oldList.get i ⟩
                   , ⟨ T, λ oldList oldElement newList => ∃ i, newList = oldList.remove i ∧ oldElement = oldList.get i ⟩
                   ],
        internals := []
      }

def composed_threemerge T :=
  let merge1 := merge T;
  let merge2 := merge T;
  let prod := product merge1 merge2;
  connect prod (by { refine ⟨2, ?_⟩; simp (config := { zetaDelta := true}) at * } )
               (by { refine ⟨0, ?_⟩; simp (config := { zetaDelta := true}) at * } )
               (by { simp (config := { zetaDelta := true}) at *})

def threemerge T : Module (List T):=
  { inputs := [⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩,
               ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩,
               ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩],
    outputs := [⟨ T, λ oldList oldElement newList => ∃ i, newList = oldList.remove i ∧ oldElement = oldList.get i ⟩],
    internals := []
  }

abbrev Ident := String
deriving instance BEq for Ident

deriving instance Repr for Ident
deriving instance Hashable for Ident
deriving instance DecidableEq for Ident
deriving instance Ord for Ident

inductive ExprLow where
  | base : Ident → Ident → ExprLow
  | product : ExprLow → ExprLow → ExprLow
  | connect : ExprLow → Nat → Nat → ExprLow
  deriving Repr

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

structure IO where
  inPorts : List Nat
  outPorts : List Nat
  deriving Repr, Inhabited

deriving instance Repr for AssocList

abbrev IdentMap α := AssocList Ident α

structure ExprHigh where
  ioPorts     : List (Ident × IO)
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
  let ioList : Q(List (Ident × IO)) := q([])
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
  ] with ioPorts := [ ("merge1", {(default : IO) with inPorts := [0, 1]})
                    , ("merge2", {inPorts := [1], outPorts := [0]})
                    ]}

#eval merge3

#eval lower [ ("merge", ⟨ 2, 1 ⟩) ].toAssocList merge3

def highlow int mod := do
  higher int <| ← lower int mod

#eval highlow [ ("merge", ⟨ 2, 1 ⟩) ].toAssocList merge3

@[simp]
def getIO.{u₁, u₂} {S : Type u₁} (l: List ((T : Type u₂) × (S -> T -> S -> Prop))) (n : Nat): ((T : Type u₂) × (S -> T -> S -> Prop)) :=
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


section Syntax

end Syntax
section littlemodules

  @[simp]
  def queue T : Module (List T) :=
   { inputs := [⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩],
     outputs := [⟨ T, λ oldList oldElement newList =>  newList ++ [oldElement] = oldList ⟩],
     internals := []
  }

  @[simp]
  def merger T R : Module (List T × List R) :=
   { inputs := [⟨ T, λ (oldListT,oldListR) newElementT (newListT, newListR) => newListT = newElementT ::  oldListT ∧ newListR = oldListR ⟩,
                ⟨ R, λ (oldListT,oldListR) newElementR (newListT, newListR) => newListR = newElementR ::  oldListR ∧ newListT = oldListT ⟩,
   ],
     outputs := [⟨ T × R , λ (oldListT,oldListR) (elementT, elementR) (newListT, newListR) =>
       newListT ++ [elementT] = oldListT ∧
       newListR ++ [elementR] = oldListR
        ⟩],
     internals := []}

  @[simp]
  def pipelined_m TagT (m : Module Q) (wf :  m.outputs.length = 1) :=
    merge_outputs (product m (queue TagT)) ⟨0, by simp⟩  ⟨1, by simp; omega⟩

  -- We should start thinking about moving things in component libraries
  @[simp]
  def bag T : Module (List T) :=
        { inputs := [⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩],
          outputs := [⟨ T, λ oldList oldElement newList => ∃ i, newList = oldList.remove i ∧ oldElement = oldList.get i ⟩],
          internals := []}
  -- set_option trace.profiler true
  @[simp]
  def bagged_m (Q: Type _) (TagT : Type _) (m : Module Q) (wf :  m.outputs.length = 1 ∧ m.inputs.length = 1) :=
    let pipe := pipelined_m TagT m wf.1;
    let prod := product pipe (bag (m.outputs[0].1 × TagT));
    connect prod ⟨2, by sorry⟩ ⟨0, by sorry⟩ (by sorry)

  @[simp]
  def bagged : ExprHigh :=
  [graph|
      pipe [mod="pipe"];
      bag [mod="bag"];
      pipe -> bag [inp = 2, out = 0]; 
  ]

  def baggedl : ExprLow :=  Option.get (lower [("pipe", ⟨2,1⟩), ("bag", ⟨1,1⟩)].toAssocList bagged) rfl

  def bagged_m' (Q: Type _) (TagT : Type 0) (m : Module Q) (wf : m.outputs.length = 1 ∧ m.inputs.length = 1) := do
      build_module' baggedl [("pipe", (⟨_, pipelined_m TagT m wf.1⟩ : ((T: Type _) × Module T))),
                             ("bag", ⟨_, bag (m.outputs[0].1 × TagT)⟩)].toAssocList

  @[simp]
  def tag_complete_spec (TagT : Type 0) [_i: BEq TagT] (T : Type 0) : Module (List TagT × (TagT → Option T)) :=
        { inputs := [
          -- Complete computation
          ⟨ TagT × T, λ (oldOrder, oldMap) (tag,el) (newOrder, newMap) =>
            -- Tag must be used, but no value ready, otherwise block:
            (List.elem tag oldOrder ∧ oldMap tag = none) ∧
            newMap = (λ idx => if idx == tag then some el else oldMap idx) ∧ newOrder = oldOrder⟩
        ],
          outputs := [
            -- Allocate fresh tag
          ⟨ TagT, λ (oldOrder, oldMap) (tag) (newOrder, newMap) =>
            -- Tag must be unused otherwise block (alternatively we
            -- could an implication to say undefined behavior):
            (!List.elem tag oldOrder ∧ oldMap tag = none) ∧
            newMap = oldMap ∧ newOrder = tag :: oldOrder⟩,
            -- Dequeue + free tag
          ⟨ T, λ (oldorder, oldmap) el (neworder, newmap) =>
            -- tag must be used otherwise, but no value brought, undefined behavior:
            ∃ l tag , oldorder = l ++ [tag] ∧ oldmap tag = some el ∧
            newmap = (λ idx => if idx == tag then none else oldmap idx) ∧ neworder = l ⟩,
            ],
          internals := []}

  @[simp]
  def tagged_ooo_h : ExprHigh :=
  [graph|
      tagger [mod="tag"];
      bagged [mod="bag"];
      merger [mod="merge"];
      -- Match tag and input
      tagger -> merger [inp = 0, out = 0];
      -- Feed the pair to the bag
      merger -> bagged [inp = 0, out = 0];
      -- Output of the bag complete inside the tagger
      bagged -> tagger [inp = 0, out = 0];
      
      -- Top-level inputs: The second input to merger which is unbound
      -- Top-level outputs: Second output of the tagger which is unbound
    ]

  @[simp]
  def tagged_ooo_l : ExprLow :=  Option.get (lower [("tag", ⟨1,2⟩), ("bag", ⟨1,1⟩), ("merge", ⟨2,1⟩)].toAssocList tagged_ooo_h) (Eq.refl _)

end littlemodules

namespace mergemod

def inPort (i : Ident) : Ident × IO :=
  (i, {inPorts := [0], outPorts := []})

def outPort (i : Ident) : Ident × IO :=
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

def fromConnection (l : List Connection) (instances : List Ident): List (Ident × IO) :=
  l.foldl (λ lcon conn => 
    if conn.inputInstance ∈ instances
    then if lcon.any (·.1 == conn.inputInstance)
         then lcon.replaceF λ a => if a.1 == conn.inputInstance then some (a.1, {a.2 with inPorts := a.2.inPorts ++ [conn.inputPort]}) else none
         else lcon ++ [(conn.inputInstance, {inPorts := [conn.inputPort], outPorts := []})]
    else if lcon.any (·.1 == conn.outputInstance)
         then lcon.replaceF λ a => if a.1 == conn.outputInstance then some (a.1, {a.2 with outPorts := a.2.outPorts ++ [conn.outputPort]}) else none
         else lcon ++ [(conn.outputInstance, {outPorts := [conn.outputPort], inPorts := []})]) []

def appendIO (a b : IO) : IO :=
  { inPorts := a.inPorts ++ b.inPorts, outPorts := a.outPorts ++ b.outPorts }

def mergeLists (l1 l2 : List (Ident × IO)) : List (Ident × IO) :=
  (RBMap.ofList l1 compare).mergeWith (λ _ => appendIO) (RBMap.ofList l2 compare) |>.toList

def sortIO' (a : IO) : IO :=
  { inPorts := a.inPorts.mergeSort (r := (· ≤ ·)), outPorts := a.outPorts.mergeSort (r := (· ≤ ·)) }

def sortIO (a : List (Ident × IO)) : List (Ident × IO) := 
  a.map λ (a, b) => (a, sortIO' b)

def _root_.DataflowRewriter.ExprHigh.subgraph (e : ExprHigh) (instances : List Ident) : ExprHigh :=
  let new_modules := e.modules.filterKeys (· ∈ instances)
  let new_connections := e.connections.filter λ a => a.inputInstance ∈ instances && a.outputInstance ∈ instances
  let generated_io := (e.connections.filter λ a => 
    a.inputInstance ∈ instances || a.outputInstance ∈ instances).removeAll new_connections
  let new_io_ports := e.ioPorts.filter λ s => s.1 ∈ instances
  { ioPorts := fromConnection generated_io instances |> mergeLists new_io_ports |> sortIO, 
    modules := new_modules, 
    connections := new_connections }

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


@[simp]
def mergeLow : ExprLow :=
  let merge1 := ExprLow.base "merge1" "merge";
  let merge2 := ExprLow.base "merge2" "merge";
  let prod := ExprLow.product merge1 merge2;
  ExprLow.connect prod 2 0

@[simp]
def merge_sem (T: Type _) :=
  match build_module' mergeLow [("merge", ⟨List T, merge T⟩)].toAssocList with
  | some x => x
  | none => ⟨Unit, empty⟩

theorem perm_erase {α : Type _} [DecidableEq α] (l₁ l₂ : List α) i:
  l₁.Perm l₂ →
  (l₁.erase i).Perm (l₂.erase i) := by
  intro H; induction H generalizing i with
  | nil => simp
  | cons x l1 l2 =>
    rename_i l1' l2'
    rw [List.erase_cons]
    rw [List.erase_cons]
    split_ifs <;> simp [*]
  | swap x y l =>
    rw [List.erase_cons]
    rw [List.erase_cons]
    rw [List.erase_cons]
    rw [List.erase_cons]
    split_ifs <;> (try simp [*])
    · simp [*] at *
      rename_i H1 H2; rw [H1,H2]
    · simp [*] at *; apply List.Perm.swap
  | trans _ _ H1 H2 =>
    rename_i l₃ _ _
    trans; apply H1; simp [*]

theorem interface_match T :  matching_interface (merge_sem T).snd (threemerge T) := by
  constructor <;> (intro ident; fin_cases ident) <;> rfl

attribute [simp] AssocList.find? BEq.beq decide instIdentDecidableEq instDecidableEqString String.decEq

theorem correct_threeway {T: Type _} [DecidableEq T]:
    refines ((merge_sem T).snd) (threemerge T) (interface_match T)
          (fun x y => (x.1 ++ x.2).Perm y) := by
      simp [threemerge, refines]
      intro x1 x2 y He indis
      rcases indis with ⟨indisL, indisR⟩
      constructor <;> dsimp at *
      . intro ident mid_i v Hi
        (fin_cases ident <;> dsimp at *)
        · constructor; constructor; and_intros
          · rfl
          · apply existSR.done
          · rcases Hi with ⟨ Hl, Hr ⟩
            rw [Hl]; subst x2
            simp [*]
          · constructor <;> dsimp only
            · intro ident' new_i v_1 Hrule
              fin_cases ident' <;> simp
            · intros ident' new_i v_1 HVal
              fin_cases ident'; simp
              reduce at *
              rcases Hi with ⟨ Hil, Hir ⟩
              rcases HVal with ⟨ ⟨ i, HVall, temp ⟩, HValr ⟩
              subst x2; subst v_1
              generalize h : mid_i.2.get i = y'
              have Ht : ∃ i, mid_i.2.get i = y' := by exists i
              rw [← List.mem_iff_get] at Ht
              have Hiff := List.Perm.mem_iff (a := y') He
              have Ht' : y' ∈ y := by rw [← Hiff]; simp; tauto
              rw [List.mem_iff_get] at Ht'
              rcases Ht' with ⟨ i', Ht'r ⟩
              constructor; exists i' + 1
              simp; tauto
        · constructor; constructor; and_intros
          · rfl
          · apply existSR.done
          · rcases Hi with ⟨ Hl, Hr ⟩
            rw [Hl]; subst x2
            simp [*]
          · constructor
            · intros ident' new_i v_1 Hrule
              fin_cases ident' <;> simp
            · intros ident' new_i v_1 HVal
              fin_cases ident'; simp
              reduce at *
              rcases Hi with ⟨ Hil, Hir ⟩
              rcases HVal with ⟨ ⟨ i, HVall, temp ⟩, HValr ⟩
              subst x2; subst v_1
              generalize h : mid_i.2.get i = y'
              have Ht : ∃ i, mid_i.2.get i = y' := by exists i
              rw [← List.mem_iff_get] at Ht
              have Hiff := List.Perm.mem_iff (a := y') He
              have Ht' : y' ∈ y := by rw [← Hiff]; simp; tauto
              rw [List.mem_iff_get] at Ht'
              rcases Ht' with ⟨ i', Ht'r ⟩
              constructor; exists i' + 1
              simp; tauto
        · constructor; constructor; and_intros
          · rfl
          · apply existSR.done
          · rcases Hi with ⟨ Hl, Hr ⟩
            rw [Hl]; subst x1
            rw [List.perm_comm]
            apply List.perm_cons_append_cons; rw [List.perm_comm]; assumption
          · constructor
            · intros ident' new_i v_1 Hrule
              fin_cases ident' <;> simp
            · intros ident' new_i v_1 HVal
              fin_cases ident'; simp
              reduce at *
              rcases Hi with ⟨ Hil, Hir ⟩
              rcases HVal with ⟨ ⟨ i, HVall, temp ⟩, HValr ⟩
              subst x1; subst v_1
              generalize h : mid_i.2.get i = y'
              have Ht : ∃ i', mid_i.2.get i' = y' := by exists i
              rw [← List.mem_iff_get] at Ht
              -- FAILS???: rw [Hil] at Ht
              have Ht' : y' ∈ v :: x2 := by rw [← Hil]; assumption
              rcases Ht' with _ | Ht'
              · constructor; exists 0
              · rename_i Ht';
                have Hiff := List.Perm.mem_iff (a := y') He
                have : y' ∈ y := by rw [← Hiff]; simp; tauto
                rw [List.mem_iff_get] at this
                rcases this with ⟨ i, Hl ⟩
                constructor; exists i + 1
                simp; tauto
      . intro ident mid_i v Hi
        fin_cases ident <;> dsimp only at * <;> reduce at *
        rcases Hi with ⟨ ⟨ i, Hil ⟩, Hir ⟩
        reduce at *
        rcases Hil with ⟨ Hill, Hilr ⟩
        subst v; subst x1
        generalize Hx2get : x2.get i = v'
        have Hx2in : v' ∈ x2 := by rw [List.mem_iff_get]; tauto
        have Hiff := List.Perm.mem_iff (a := v') He
        have Hyin : v' ∈ y := by rw [← Hiff]; simp; tauto
        rw [List.mem_iff_get] at Hyin
        rcases Hyin with ⟨ i', Hyget ⟩
        have HerasePerm : (mid_i.1.append mid_i.2).Perm (y.eraseIdx i'.1) := by
          simp [Hill]
          trans; apply List.perm_append_comm
          rw [←List.eraseIdx_append_of_lt_length] <;> [skip; apply i.isLt]
          trans ((x2 ++ mid_i.1).erase x2[i])
          have H2 : x2[i] = (x2 ++ mid_i.1)[i] := by
            symm; apply List.getElem_append_left
          rw [H2]; symm; apply List.erase_get
          symm; trans; symm; apply List.erase_get
          rw [Hyget]; simp at Hx2get; simp; rw [Hx2get]
          apply perm_erase; symm
          symm; trans; symm; assumption
          apply List.perm_append_comm
        constructor; constructor; and_intros
        · exists i'; and_intros; rfl; tauto
        · apply existSR.done
        · assumption
        · constructor <;> dsimp only
          · intro ident' new_i v_1 Hrule
            fin_cases ident' <;> simp
          · intros ident' new_i v_1 HVal
            fin_cases ident'
            reduce at *
            rcases HVal with ⟨ ⟨ i'', HVall, temp ⟩, HValr ⟩
            subst v'; subst v_1
            dsimp at *
            have : mid_i.2[i''] ∈ (x2.eraseIdx i.1) := by
              simp [Hill]; apply List.getElem_mem
            have : mid_i.2[i''] ∈ (mid_i.1 ++ x2.eraseIdx i.1) := by
              rw [List.mem_eraseIdx_iff_getElem] at this; simp; right
              simp at *; simp [Hill]; apply List.getElem_mem
            have HPermIn : mid_i.2[i''] ∈ y.eraseIdx i' := by
              rw [List.Perm.mem_iff]; assumption; symm
              rw [←Hill]; assumption
            rw [List.mem_iff_getElem] at HPermIn
            rcases HPermIn with ⟨ Ha, Hb, Hc ⟩
            constructor; exists ⟨ Ha, Hb ⟩; tauto
      · intro ident mid_i Hv
        fin_cases ident
        rcases Hv with ⟨ la, lb, vout, ⟨ ⟨ i, H2, H3 ⟩, Hx3 ⟩, ⟨ Hx2, H4 ⟩ ⟩; subst lb; subst la; subst vout
        constructor; and_intros
        · apply existSR.done
        · rw [Hx2,← H4,←List.eraseIdx_append_of_lt_length] <;> [skip; apply i.isLt]
          dsimp only;
          trans ((x1 ++ x1[i] :: x2).erase x1[i])
          rw [List.perm_comm]
          have : x1[↑i] = x1.get i := by simp
          simp [*] at *
          have H : x1[↑i] = (x1 ++ x1[↑i] :: x2)[↑i] := by
            symm; apply List.getElem_append_left
          dsimp at *; conv => arg 1; arg 2; rw [H]
          apply List.erase_get
          trans ((x1[i] :: (x1 ++ x2)).erase x1[i])
          apply perm_erase; simp
          rw [List.erase_cons_head]; assumption
        · constructor
          · intros ident' new_i v_1 Hrule
            fin_cases ident' <;> simp
          · intros ident' new_i v_1 HVal
            fin_cases ident'
            reduce at *
            rcases HVal with ⟨ ⟨ i', _, temp ⟩, _ ⟩
            subst v_1
            generalize h : mid_i.2.get i' = y'
            have Ht : ∃ i', mid_i.2.get i' = y' := by exists i'
            rw [← List.mem_iff_get] at Ht
            have Hiff := List.Perm.mem_iff (a := y') He
            have Ht'' : y' ∈ x1.get i :: x2 := by rw [←Hx2]; assumption
            simp at Ht''; rcases Ht'' with (Ht'' | Ht'')
            · have Ht' : y' ∈ y := by
                rw [List.Perm.mem_iff]; rotate_left; rewrite [List.perm_comm]; assumption; subst y'
                rw [Ht'']; simp; left; apply List.getElem_mem
              dsimp; apply List.getElem_of_mem at Ht'; rcases Ht' with ⟨ Ha, Hb, Hc ⟩
              constructor; exists ⟨ Ha, Hb ⟩; and_intros; rfl; symm; assumption
            · have Ht' : y' ∈ y := by
                rw [List.Perm.mem_iff]; rotate_left; rewrite [List.perm_comm]; assumption; subst y'
                simp; tauto
              dsimp; apply List.getElem_of_mem at Ht'; rcases Ht' with ⟨ Ha, Hb, Hc ⟩
              constructor; exists ⟨ Ha, Hb ⟩; and_intros; rfl; symm; assumption

section RefinementTheorem

end RefinementTheorem


end DataflowRewriter
