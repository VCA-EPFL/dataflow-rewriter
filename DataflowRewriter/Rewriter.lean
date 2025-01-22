/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.ExprHigh
import Lean.Data.Json

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

inductive RewriteType where
| rewrite
| abstraction
| concretisation
deriving Repr, Inhabited

structure RewriteInfo where
  type : RewriteType
  input_graph : ExprHigh String
  output_graph : ExprHigh String
  matched_subgraph : List String
  renamed_input_nodes : AssocList String (Option String)
  new_output_nodes : List String
  debug : Option String := .none
  name : Option String := .none
  deriving Repr, Inhabited

instance : Lean.ToJson RewriteInfo where
  toJson r :=
    Lean.Json.mkObj
      [ ("type", Lean.Format.pretty <| repr r.type)
      , ("name", Lean.toJson r.name)
      , ("input_graph", toString r.input_graph)
      , ("output_graph", toString r.output_graph)
      , ("matched_subgraph", Lean.toJson r.matched_subgraph)
      , ("renamed_input_nodes", Lean.Json.mkObj <| r.renamed_input_nodes.toList.map (λ a => (a.1, Lean.toJson a.2)))
      , ("new_output_nodes", Lean.toJson r.new_output_nodes)
      , ("debug", Lean.toJson r.debug)
      ]

abbrev RewriteResult := EStateM RewriteError (List RewriteInfo)

section Rewrite

variable (Ident)
variable [DecidableEq Ident]

@[simp] abbrev Pattern := ExprHigh Ident → RewriteResult (List Ident × List Ident)

structure Abstraction where
  pattern : Pattern Ident
  typ : Ident

structure Concretisation where
  expr : ExprLow Ident
  typ : Ident
deriving Repr, Inhabited

structure DefiniteRewrite where
  input_expr : ExprLow Ident
  output_expr : ExprLow Ident

structure Rewrite where
  pattern : Pattern Ident
  rewrite : List Ident → Option (DefiniteRewrite Ident)
  abstractions : List (Abstraction Ident) := []
  name : Option String := .none

variable {Ident}
variable [Inhabited Ident]

def ofOption {ε α σ} (e : ε) : Option α → EStateM ε σ α
| some o => pure o
| none => throw e

def liftError {α σ} : Except String α → EStateM RewriteError σ α
| .ok o => pure o
| .error s => throw (.error s)

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
        let inst' := "tmp_" ++ fresh_prefix ++ toString n
        let nameMap' := nameMap.cons inst inst'
        go (n+1) nameMap' (p.cons ⟨.internal inst, name⟩ ⟨.internal inst', name⟩) b
    | ⟨.top, name⟩ :: b => go n nameMap p b
    | [] => (p, nameMap)

def comm_connection {Ident} [DecidableEq Ident] (conn : Connection Ident) : ExprLow Ident → ExprLow Ident
| orig@(.connect o i e) =>
  if o = conn.output ∧ i = conn.input then
    match e with
    | .connect o' i' e' =>
      if o ≠ o' ∨ i ≠ i' then
        .connect o' i' (comm_connection conn <| .connect o i e')
      else orig
    | _ => orig
  else .connect o i <| comm_connection conn e
| .product e₁ e₂ =>
  .product (comm_connection conn e₁) (comm_connection conn e₂)
| e => e

def comm_connections {Ident} [DecidableEq Ident] (conn : List (Connection Ident)) (e : ExprLow Ident): ExprLow Ident :=
  conn.foldr comm_connection e

def portmappingToNameRename' (sub : List String) (p : PortMapping String) : RewriteResult (AssocList String (Option String)) :=
  p.input.foldlM
    (λ | (a : AssocList String (Option String)), ⟨.internal lport, _⟩, ⟨.internal rport, _⟩ =>
         match a.find? lport with
         | .some x => do
           if lport ∈ sub && x = .none then return a
           if x = .some rport then return a
           throw (.error s!"instance names don't match: {x} != {rport} for {lport}")
         | .none => do
           if lport ∈ sub then return a.cons lport .none
           return a.cons lport (.some rport)
       | a, _, _ => pure a
       ) ∅

def addRewriteInfo (rinfo : RewriteInfo) : RewriteResult Unit := do
  let l ← EStateM.get
  EStateM.set <| l.concat rinfo

def EStateM.guard {ε σ} (e : ε) (b : Bool) : EStateM ε σ Unit :=
  if b then pure () else EStateM.throw e

/--
Perform a rewrite in the graph by lowering it into an inductive expression using the right ordering, replacing it, and
then reconstructing the graph.

In the process, all names are generated again so that they are guaranteed to be fresh.  This could be unnecessary,
however, currently the low-level expression language does not remember any names.
-/
@[drunfold] def Rewrite.run' (fresh_prefix : String) (g : ExprHigh String) (rewrite : Rewrite String)
  : RewriteResult (ExprHigh String) := do

  -- Pattern match on the graph and extract the first list of nodes that correspond to the first subgraph.
  let (sub, types) ← rewrite.pattern g
  let def_rewrite ← ofOption (.error s!"types {repr types} are not correct for rewrite {fresh_prefix}") <| rewrite.rewrite types

  -- Extract the actual subgraph from the input graph using the list of nodes `sub`.
  let (g₁, g₂) ← ofOption (.error "could not extract graph") <| g.extract sub

  -- Lower the subgraph g₁ to an `ExprLow` expression.
  let e_sub ← ofOption (.error "could not lower subgraph: graph is empty") <| g₁.lower

  -- g_lower is the fully lowered graph with the sub expression that is to be replaced rearranged so that it can be
  -- pattern matched.
  let g_lower := g₂.lower' e_sub

  -- beq is an α-equivalence check that returns a mapping to rename one expression into the other.  This mapping is
  -- split into the external mapping and internal mapping.
  let (ext_mapping, int_mapping) ← liftError <| e_sub.weak_beq def_rewrite.input_expr

  let comb_mapping := ExprLow.filterId <| ext_mapping.append int_mapping
  EStateM.guard (.error "input mapping not invertible") <| ExprLow.invertible comb_mapping.input
  EStateM.guard (.error "output mapping not invertible") <| ExprLow.invertible comb_mapping.output

  -- We rewrite the output expression external ports to match the external ports of the internal expression it is
  -- replacing.  In addition to that, we also rename the internal ports of the input_expr so that they match the
  -- internal ports of the extracted subgraph.  We apply the same renaming map to the output_expr, which will mainly
  -- just rename the external ports though.
  let e_sub_output := def_rewrite.output_expr.renamePorts comb_mapping
  let e_sub_input := def_rewrite.input_expr.renamePorts comb_mapping

  -- We are now left with `e_sub_output` which contains an expression where the external ports are renamed, and the
  -- internal ports have not been renamed from the original graph.  `e_sub_input` where all signals have been renamed so
  -- that e_sub_input has all the same internal and external wire names, even though it won't be structurally equal to
  -- `e_sub` yet.  For that we will have to canonicalise both sides.

  -- We then return all internal variable names so that we can generate fresh names for them.
  let (e_sub'_vars_i, e_sub'_vars_o) := e_sub_output.allVars
  let (inputPortMap, nameMap) := generate_renaming ∅ fresh_prefix (e_sub'_vars_i.filter (λ x => x ∉ ext_mapping.input.keysList))
  let (outputPortMap, nameMap') := generate_renaming nameMap fresh_prefix (e_sub'_vars_o.filter (λ x => x ∉ ext_mapping.output.keysList))
  let int_mapping' : PortMapping String := ⟨ inputPortMap, outputPortMap ⟩

  -- We then rename all internal signals in the new expression with the fresh
  -- names.
  let e_renamed_output_sub := e_sub_output.renamePorts int_mapping'
  let e_renamed_input_sub := e_sub_input.renamePorts int_mapping'

  -- Finally we do the actual replacement.

  -- `norm` is a function that canonicalises the connections of the input expression given a list of connections as the
  -- ordering guide.
  let canon := comm_connections g₁.connections
  let rewritten := (canon g_lower).replace (canon e_renamed_input_sub) e_renamed_output_sub

  let norm := rewritten.normalisedNamesMap fresh_prefix
  let out ← rewritten.renamePorts norm |>.higherSS |> ofOption (.error "could not lift expression to graph")
  let portMap ← portmappingToNameRename' sub norm
  let inputPortMap := portMap.filter (λ lhs _ => ¬ nameMap'.inverse.contains lhs)
  let outputPortMap := portMap.filter (λ lhs _ => nameMap'.inverse.contains lhs)
  addRewriteInfo <| RewriteInfo.mk RewriteType.rewrite g out sub inputPortMap (outputPortMap.toList.map Prod.snd |>.reduceOption) .none rewrite.name
  return out

/--
Abstract a subgraph into a separate node.  One can imagine that the node type is then a node in the environment which is
referenced in the new graph.

These two functions do not have to have any additional proofs, because the proofs that are already present in the
framework should be enough.
-/
@[drunfold] def Abstraction.run (fresh_prefix : String) (g : ExprHigh String)
  (abstraction : Abstraction String)
  : RewriteResult (ExprHigh String × Concretisation String) := do
  let (sub, _) ← abstraction.pattern g
  let (g₁, g₂) ← ofOption (.error "could not extract graph") <| g.extract sub
  let e_sub ← ofOption (.error "could not lower subgraph: graph is empty") <| g₁ |>.lower
  let g_lower := g₂ |>.lower' e_sub

  -- Here we have to make sure that the context contains a renamed version of e_sub to show equivalence to the
  -- abstracted version, because the abstracted version has `.top` IO ports.  These are needed because of the matcher
  -- that comes in the second phase.
  let portMapping := e_sub.build_interface.toIdentityPortMapping' -- abstraction.typ
  let abstracted := g_lower.abstract e_sub portMapping abstraction.typ
  let e_sub' := e_sub.renamePorts portMapping.inverse

  -- let portMapping := e_sub.build_interface.toIdentityPortMapping -- abstraction.typ
  -- let abstracted := g_lower.abstract e_sub portMapping abstraction.typ
  -- let e_sub' := e_sub
  let norm := abstracted.normalisedNamesMap fresh_prefix
  let highered ← abstracted.renamePorts norm |>.higherSS |> ofOption (.error "Could not normalise names")
  let portMap ← portmappingToNameRename' sub norm
  addRewriteInfo <| RewriteInfo.mk RewriteType.abstraction g highered sub
                      portMap [abstraction.typ] .none (.some s!"{abstraction.typ}")
  return (highered, ⟨e_sub', abstraction.typ⟩)
  -- return (abstracted.higherS fresh_prefix, ⟨e_sub, abstraction.typ⟩)

/--
Can be used to concretise the abstract node again.  Currently it assumes that it is unique in the graph (which could be
checked explicitly).  In addition to that, it currently assumes that the internal signals of the concretisation are
still fresh in the graph.
-/
@[drunfold] def Concretisation.run (fresh_prefix : String) (g : ExprHigh String)
  (concretisation : Concretisation String) : RewriteResult (ExprHigh String) := do
  let g_lower ← ofOption (.error "could not lower graph") <| g.lower
  -- may need to uniquify the concretisation internal connections
  let base ← ofOption (.error "Could not find base of concretisation")
    <| g_lower.findBase concretisation.typ
  -- return g_lower.concretise (concretisation.expr.renameMapped base) base concretisation.typ
  --        |>.higherS fresh_prefix
  let e_sub := concretisation.expr.renamePorts base
  let concr := g_lower.concretise e_sub base concretisation.typ
  let norm := concr.normalisedNamesMap fresh_prefix
  let concr_g ← concr.renamePorts norm |>.higherSS |> ofOption (.error "Could not normalise names")
  let portMap ← portmappingToNameRename' [concretisation.typ] norm
  let outputPortMap := portMap.filter (λ lhs _ => lhs = concretisation.typ)
  addRewriteInfo <| RewriteInfo.mk RewriteType.concretisation g concr_g [concretisation.typ] portMap
                      (outputPortMap.toList.map Prod.snd |>.reduceOption) .none (.some s!"{concretisation.typ}")
  return concr_g

@[drunfold] def Rewrite.run (fresh_prefix : String) (g : ExprHigh String) (rewrite : Rewrite String)
  : RewriteResult (ExprHigh String) := do
  let (g, c, _) ← rewrite.abstractions.foldlM (λ (g', c', n) a => do
      let (g'', c'') ← a.run (fresh_prefix ++ s!"_A_{n}_") g'
      return (g'', c''::c', n+1)
    ) (g, [], 0)
  let g ← rewrite.run' (fresh_prefix ++ s!"_R_") g
  c.foldlM (λ (g, n) (c : Concretisation String) => do
    let g' ← c.run (fresh_prefix ++ s!"_C_{n}_") g
    return (g', n+1)) (g, 0) |>.map Prod.fst

/--
Loops over the [rewrite] function, applying one rewrite exhaustively until moving on to the next.  Maybe we should add a
timeout for each single rewrite as well, so that infinite loops in a single rewrite means the next one can still be
started.
-/
def rewrite_loop' (orig_n : Nat) (pref : String) (g : ExprHigh String)
    : (rewrites : List (Rewrite String)) → Nat → RewriteResult (ExprHigh String)
| _, 0 | [], _ => return g
| r :: rs, fuel' + 1 =>
  try
    let g' ← r.run (pref ++ "_f" ++ toString (orig_n - fuel') ++ "_l" ++ toString (List.length <| r :: rs) ++ "_") g
    rewrite_loop' orig_n pref g' (r :: rs) fuel'
  catch
  | .done => rewrite_loop' orig_n pref g rs orig_n
  | .error s => throw <| .error s

def rewrite_loop (g : ExprHigh String) (rewrites : List (Rewrite String)) (pref : String := "rw") (depth : Nat := 10000)
    : RewriteResult (ExprHigh String) :=
  rewrite_loop' depth pref g rewrites depth

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
  (followOutput' g inst ⟨.top, output⟩).run' default

def followOutputFull (g : ExprHigh String) (inst : String) (output : InternalPort String) : Option (NextNode String) :=
  (followOutput' g inst output).run' default

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
  (followInput' g inst input).run' default

def findType (g : ExprHigh String) (typ : String) : List String :=
  g.modules.foldl (λ l a b => if b.snd = typ then a :: l else l) []

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

def extractType (s : String) : String :=
  let parts := s.splitOn " "
  parts.tail.foldl (λ a b => a ++ " " ++ b) "" |>.drop 1

end DataflowRewriter
