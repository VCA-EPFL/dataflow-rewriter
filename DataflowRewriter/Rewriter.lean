/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.ExprHigh
import DataflowRewriter.ExprHighElaborator

open Batteries (AssocList)

namespace DataflowRewriter

inductive RewriteError where
| error (s : String)
| done
deriving Repr

instance : ToString RewriteError where
  toString
  | .error s => s!"error: {s}"
  | .done => s!"done"

abbrev RewriteResult := Except RewriteError

section Rewrite

variable (Ident)
variable [DecidableEq Ident]

@[simp] abbrev Pattern := ExprHigh Ident → RewriteResult (List Ident)

structure Abstraction where
  pattern : Pattern Ident
  typ : Ident

structure Concretisation where
  expr : ExprLow Ident
  typ : Ident
deriving Repr, Inhabited

structure Rewrite where
  pattern : Pattern Ident
  input_expr : ExprLow Ident
  output_expr : ExprLow Ident
  abstractions : List (Abstraction Ident) := []

variable {Ident}
variable [Inhabited Ident]

def ofOption {α ε} (e : ε) : Option α → Except ε α
| some o => .ok o
| none => .error e

def liftError {α} : Except String α → Except RewriteError α
| .ok o => .ok o
| .error s => .error (.error s)

end Rewrite

def generate_renaming (nameMap : AssocList String String) (fresh_prefix : String) (internals : List (InternalPort String)) :=
  go 0 nameMap ∅ internals
  where
    go (n : Nat) (nameMap : AssocList String String) (p : PortMap String (InternalPort String))
      : List (InternalPort String) → PortMap String (InternalPort String) × AssocList String String
    | (⟨.internal inst, name⟩) :: b =>
      match nameMap.find? inst with
      | some inst' => go n nameMap (p.cons ⟨.internal inst, name⟩ ⟨.internal inst', name⟩) b
      | none =>
        let inst' := fresh_prefix ++ toString n
        let nameMap' := nameMap.cons inst inst'
        go (n+1) nameMap' (p.cons ⟨.internal inst, name⟩ ⟨.internal inst', name⟩) b
    | ⟨.top, name⟩ :: b => go n nameMap p b
    | [] => (p, nameMap)

/--
Perform a rewrite in the graph by lowering it into an inductive expression using
the right ordering, replacing it, and then reconstructing the graph.

In the process, all names are generated again so that they are guaranteed to be
fresh.  This could be unnecessary, however, currently the low-level expression
language does not remember any names.
-/
@[drunfold] def Rewrite.run (fresh_prefix : String) (g : ExprHigh String) (rewrite : Rewrite String)
  : RewriteResult (ExprHigh String) := do
  let sub ← rewrite.pattern g
  let (g₁, g₂) ← ofOption (.error "could not extract graph") <| g.extract sub
  let e_sub ← ofOption (.error "could not lower subgraph: graph is empty") <| g₁.lower
  let g_lower := g₂.lower' e_sub
  -- dbg_trace s!"e_sub:: {repr e_sub}\n\nrewrite.input_expr:: {repr rewrite.input_expr}"
  let (ext_mapping, _) ← liftError <| e_sub.beq rewrite.input_expr
  let e_sub' := rewrite.output_expr.renameMapped ext_mapping.inverse
  let (e_sub'_vars_i, e_sub'_vars_o) := e_sub'.allVars
  let (inputPortMap, nameMap) := generate_renaming ∅ fresh_prefix (e_sub'_vars_i.filter (λ x => x ∉ ext_mapping.input.keysList))
  let (outputPortMap, _) := generate_renaming nameMap fresh_prefix (e_sub'_vars_o.filter (λ x => x ∉ ext_mapping.output.keysList))
  let int_mapping' : PortMapping String := ⟨ inputPortMap, outputPortMap ⟩
  let e_renamed_sub' := e_sub'.renameMapped int_mapping'
  return g_lower.replace e_sub e_renamed_sub' |>.higherS fresh_prefix

/--
Abstract a subgraph into a separate node.  One can imagine that the node type is
then a node in the environment which is referenced in the new graph.

These two functions do not have to have any additional proofs, because the
proofs that are already present in the framework should be enough.
-/
@[drunfold] def Abstraction.run (fresh_prefix : String) (g : ExprHigh String)
  (abstraction : Abstraction String)
  : RewriteResult (ExprHigh String × Concretisation String) := do
  let sub ← abstraction.pattern g
  let (g₁, g₂) ← ofOption (.error "could not extract graph") <| g.extract sub
  let e_sub ← ofOption (.error "could not lower subgraph: graph is empty") <| g₁ |>.lower
  let g_lower := g₂ |>.lower' e_sub
  /- Here we have to make sure that the context contains a renamed version of
  e_sub to show equivalence to the abstracted version, because the abstracted
  version has `.top` IO ports -/
  let portMapping := e_sub.build_interface.toIdentityPortMapping' -- abstraction.typ
  let abstracted := g_lower.abstract e_sub portMapping abstraction.typ
  let e_sub' := e_sub.renameMapped portMapping.inverse
  return (abstracted.higherS fresh_prefix, ⟨e_sub', abstraction.typ⟩)
  -- return (abstracted.higherS fresh_prefix, ⟨e_sub, abstraction.typ⟩)

/--
Can be used to concretise the abstract node again.  Currently it assumes
that it is unique in the graph (which could be checked explicitly).  In addition
to that, it currently assumes that the internal signals of the concretisation
are still fresh in the graph.
-/
@[drunfold] def Concretisation.run (fresh_prefix : String) (g : ExprHigh String)
  (concretisation : Concretisation String) : RewriteResult (ExprHigh String) := do
  let g_lower ← ofOption (.error "could not lower graph") <| g.lower
  -- may need to uniquify the concretisation internal connections
  let base ← ofOption (.error "Could not find base of concretisation")
    <| g_lower.findBase concretisation.typ
  -- return g_lower.concretise (concretisation.expr.renameMapped base) base concretisation.typ
  --        |>.higherS fresh_prefix
  dbg_trace s!"{repr <| concretisation.typ}"
  dbg_trace s!"{repr <| concretisation.expr.renameMapped base}"
  let e_sub := concretisation.expr.renameMapped base
  return g_lower.concretise e_sub base concretisation.typ |>.higherS fresh_prefix

@[drunfold] def rewrite (fresh_prefix : String) (g : ExprHigh String) (rewrite : Rewrite String)
  : RewriteResult (ExprHigh String) := do
  let (g, c, _) ← rewrite.abstractions.foldlM (λ (g', c', n) a => do
      let (g'', c'') ← a.run (fresh_prefix ++ s!"_A_{n}_") g'
      return (g'', c''::c', n+1)
    ) (g, [], 0)
  let g ← rewrite.run (fresh_prefix ++ s!"_R_") g
  dbg_trace s!"before: {repr g}"
  c.foldlM (λ (g, n) (c : Concretisation String) => do
    let g' ← c.run (fresh_prefix ++ s!"_C_{n}_") g
    return (g', n+1)) (g, 0) |>.map Prod.fst

/--
Loops over the [rewrite] function, applying one rewrite exhaustively until
moving on to the next.  Maybe we should add a timeout for each single rewrite as
well, so that infinite loops in a single rewrite means the next one can still be
started.
-/
def rewrite_loop (pref : String) (g : ExprHigh String)
    : (rewrites : List (Rewrite String)) → Nat → RewriteResult (ExprHigh String)
| _, 0 | [], _ => return g
| r :: rs, fuel' + 1 => do
  let g' ← try rewrite (pref ++ toString fuel' ++ "_") g r
            catch
            | .done => rewrite_loop pref g rs fuel'
            | .error s => throw <| .error s
  rewrite_loop pref g' (r :: rs) fuel'

structure NextNode (Ident) where
  inst : Ident
  inputPort : Ident
  portMap : PortMapping Ident
  typ : Ident
  connection : Connection Ident
deriving Repr

/--
Follow an output to the next node.  A similar function could be written to
follow the input to the previous node.
-/
def followOutput' (g : ExprHigh String) (inst : String) (output : InternalPort String) : RewriteResult (NextNode String) := do
  let (pmap, _) ← ofOption (.error "instance not in modules")
    <| g.modules.find? inst
  let localOutputName ← ofOption (.error "port not in instance portmap")
    <| pmap.output.find? output
  let c@⟨_, localInputName⟩ ← ofOption (.error "output not in connections")
    <| g.connections.find? (λ c => c.output = localOutputName)
  let (inst, iport) ← ofOption (.error "input port not in modules")
    <| ExprHigh.findInputPort' localInputName g.modules
  ofOption (.error "instance not in modules") <| (g.modules.findEntry? inst).map (λ x => ⟨inst, iport, x.2.1, x.2.2, c⟩)

def followOutput (g : ExprHigh String) (inst output : String) : Option (NextNode String) :=
  (followOutput' g inst ⟨.top, output⟩).toOption

def followOutputFull (g : ExprHigh String) (inst : String) (output : InternalPort String) : Option (NextNode String) :=
  (followOutput' g inst output).toOption

/--
Follow an output to the next node.  A similar function could be written to
follow the input to the previous node.
-/
def followInput' (g : ExprHigh String) (inst input : String) : RewriteResult (NextNode String) := do
  let (pmap, _) ← ofOption (.error "instance not in modules")
    <| g.modules.find? inst
  let localInputName ← ofOption (.error "port not in instance portmap")
    <| pmap.input.find? ⟨.top, input⟩
  let c@⟨localOutputName, _⟩ ← ofOption (.error "output not in connections")
    <| g.connections.find? (λ c => c.input = localInputName)
  let (inst, iport) ← ofOption (.error "input port not in modules")
    <| ExprHigh.findOutputPort' localOutputName g.modules
  ofOption (.error "instance not in modules") <| (g.modules.findEntry? inst).map (λ x => ⟨inst, iport, x.2.1, x.2.2, c⟩)

def followInput (g : ExprHigh String) (inst input : String) : Option (NextNode String) :=
  (followInput' g inst input).toOption

def calcSucc (g : ExprHigh String) : Option (Std.HashMap String (Array String)) :=
  g.modules.foldlM (λ succ k v => do
      let a ← v.fst.output.foldlM (λ succ' (k' v' : InternalPort String) => do
          if v'.inst.isTop then return succ'
          let out ← followOutputFull g k k'
          return succ'.push out.inst
        ) ∅
      return succ.insert k a
    ) ∅

/--
Calculate a successor hashmap for a graph which includes a single root node and
a single leaf node which connects to all inputs and all outputs respectively.
It's much easier to work on this successor structure than on the unstructured
graph.
-/
def fullCalcSucc (g : ExprHigh String) (rootNode : String := "_root_") (leafNode : String := "_leaf_") : Option (Std.HashMap String (Array String)) := do
  let succ ← calcSucc g
  let succ := succ.insert rootNode g.inputNodes.toArray
  let succ := succ.insert leafNode ∅
  return g.outputNodes.foldl (λ succ n => succ.insert n (succ[n]?.getD #[] |>.push leafNode) ) succ

structure EvalLinkState where
  ancestor : Std.HashMap String String
  label : Std.HashMap String String
deriving Repr

def link (v w : String) (s : EvalLinkState) : EvalLinkState := {s with ancestor := s.ancestor.insert w v}

def compress (v : String) (semi : Std.HashMap String Int) (s : EvalLinkState) : Nat → EvalLinkState
| 0 => s
| n+1 => Id.run do
  let mut s' := s
  if s'.ancestor[s'.ancestor[v]!]! ≠ "" then
    s' := compress s'.ancestor[v]! semi s' n
    if semi[s'.label[s'.ancestor[v]!]!]! < semi[s'.label[v]!]! then
      s' := {s' with label := s'.label.insert v s'.label[s'.ancestor[v]!]!}
    s' := {s' with ancestor := s'.ancestor.insert v s'.ancestor[s'.ancestor[v]!]!}
  return s'

def eval (fuel : Nat) (v : String) (semi : Std.HashMap String Int) (s : EvalLinkState) : String × EvalLinkState := Id.run do
  if s.ancestor[v]! = "" then
    return (v, s)
  else
    let s' := compress v semi s fuel
    return (s'.label[v]!, s)

structure DomState where
  semi : Std.HashMap String Int
  vertex : Array String
  parent : Std.HashMap String String
  pred : Std.HashMap String (Array String)
  bucket : Std.HashMap String (Array String)
  dom : Std.HashMap String String
deriving Repr

def DomState.dfs (fuel : Nat) (succ : Std.HashMap String (Array String)) (dom : DomState) (v : String) : DomState × Nat :=
  go dom v 0 fuel
  where
    go (dom : DomState) (v : String) (n : Nat) : Nat → DomState × Nat
    | 0 => (dom, n)
    | fuel+1 => Id.run do
      let mut n' := n + 1
      let mut dom' := dom
      dom' := {dom' with semi := dom'.semi.insert v n', vertex := dom'.vertex.set! n' v}
      for w in succ[v]! do
        if dom'.semi[w]! = 0 then
          dom' := {dom' with parent := dom'.parent.insert w v }
          (dom', n') := go dom' w n' fuel
        dom' := {dom' with pred := dom'.pred.insert w (dom'.pred[w]!.push v)}
      return (dom', n')

/--
Find dominators in a graph, taken from "A fast algorithm for finding dominators
in a flowgraph" by T. Lengauer and R. E. Tarjan.

Don't ask me how the algorithm works, but it seems to output reasonable results.
-/
def findDom (fuel : Nat) (g : ExprHigh String) := do
  let mut n := 0
  let mut dom : DomState := ⟨∅, ∅, ∅, ∅, ∅, ∅⟩
  let mut succ ← fullCalcSucc g
  let mut evalLabel : EvalLinkState := ⟨∅, ∅⟩
  -- succ := succ.insert "_leaf_" ∅

  -- Step 1
  dom := {dom with vertex := dom.vertex.push ""}
  for v in succ do
    dom := {dom with pred := dom.pred.insert v.fst ∅
                     semi := dom.semi.insert v.fst 0
                     bucket := dom.bucket.insert v.fst ∅
                     dom := dom.dom.insert v.fst ""
                     parent := dom.parent.insert v.fst ""
                     vertex := dom.vertex.push ""}
    evalLabel := {evalLabel with ancestor := evalLabel.ancestor.insert v.fst ""
                                 label := evalLabel.label.insert v.fst v.fst}
  (dom, n) := dom.dfs fuel succ "_root_"
  for i' in [0:n-1] do
    let i := n - i'
    let w := dom.vertex[i]!

    -- Step 2
    for v in dom.pred[w]! do
      let (u, evalLabel') := eval fuel v dom.semi evalLabel
      evalLabel := evalLabel'
      if dom.semi[u]! < dom.semi[w]! then
        dom := {dom with semi := dom.semi.insert w dom.semi[v]! }
    let vert : String := dom.vertex[dom.semi[w]!.toNat]!
    dom := {dom with bucket := dom.bucket.insert vert (dom.bucket[vert]!.push w)}
    evalLabel := link dom.parent[w]! w evalLabel

    -- Step 3
    for v in dom.bucket[dom.parent[w]!]! do
      let l := dom.bucket[dom.parent[w]!]!
      dom := {dom with bucket := dom.bucket.insert dom.parent[w]! (l.filter (· ≠ v)) }
      let (u, evalLabel') := eval fuel v dom.semi evalLabel
      evalLabel := evalLabel'
      dom := {dom with dom := dom.dom.insert v (if dom.semi[u]! < dom.semi[v]! then u else dom.parent[w]!)}

  -- Step 4
  for i in [2:n+1] do
    let w := dom.vertex[i]!
    if dom.dom[w]! ≠ dom.vertex[dom.semi[w]!.toNat]! then
      dom := {dom with dom := dom.dom.insert w dom.dom[dom.dom[w]!]!}
  dom := {dom with dom := dom.dom.insert "_root_" ""}
  return dom.dom

/--
Find post dominators of a node by finding dominators on the inverted graph.
-/
def findPostDom (fuel : Nat) (g : ExprHigh String) :=
  findDom fuel g.invert

def findSCCNodes' (succ : Std.HashMap String (Array String)) (startN endN : String) : Option (List String):=
  go (succ.size+1) ∅ [startN]
  where
    go (worklist : Nat) (visited : List String) : List String → Option (List String)
    | [] => some visited
    | x :: q => do
      match worklist with
      | 0 => none
      | w+1 =>
        let visited' := visited.cons x
        if x = endN then
          go w visited' q
        else
          let nextNodes ← succ[x]?.map (·.toList)
          if "_leaf_" ∈ nextNodes then none
          if startN ∈ nextNodes then none
          let nextNodes' := nextNodes.filter (· ∉ visited')
          go w visited' (nextNodes' ++ q)

/--
Find all nodes in between two nodes by performing a DFS that checks that one has
never reached an output node.
-/
def findSCCNodes (g : ExprHigh String) (startN endN : String) : Option (List String) := do
  let l ← findSCCNodes' (← fullCalcSucc g) startN endN
  let l' ← findSCCNodes' (← fullCalcSucc g.invert) endN startN
  return l.union l'

end DataflowRewriter
