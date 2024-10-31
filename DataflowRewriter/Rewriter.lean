/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.ExprHigh

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

structure Rewrite where
  pattern : Pattern Ident
  input_expr : ExprLow Ident
  output_expr : ExprLow Ident

variable {Ident}
variable [Inhabited Ident]

def ofOption {α ε} (e : ε) : Option α → Except ε α
| some o => .ok o
| none => .error e

def liftError {α} : Except String α → Except RewriteError α
| .ok o => .ok o
| .error s => .error (.error s)

end Rewrite

private def generate_renaming (fresh_prefix : String) (internals : List (InternalPort String)) :=
  go 0 ∅ ∅ internals
  where
    go (n : Nat) (nameMap : AssocList String String) (p : PortMap String (InternalPort String))
      : List (InternalPort String) → PortMap String (InternalPort String)
    | (⟨.internal inst, name⟩) :: b =>
      match nameMap.find? inst with
      | some inst' => go n nameMap (p.cons ⟨.internal inst, name⟩ ⟨.internal inst', name⟩) b
      | none =>
        let inst' := fresh_prefix ++ toString n
        let nameMap' := nameMap.cons inst inst'
        go n nameMap (p.cons ⟨.internal inst, name⟩ ⟨.internal inst', name⟩) b
    | ⟨.top, name⟩ :: b => go n nameMap p b
    | [] => p

@[drunfold] def rewrite (fresh_prefix : String) (g : ExprHigh String) (rewrite : Rewrite String)
  : RewriteResult (ExprHigh String) := do
  let sub ← rewrite.pattern g
  let (g₁, g₂) ← ofOption (.error "could not extract graph") <| g.extract sub
  let e_sub ← ofOption (.error "could not lower subgraph: graph is empty") <| g₁ |>.lower
  let g_lower := g₂ |>.lower' e_sub
  let (ext_mapping, _) ← liftError <| e_sub.beq rewrite.input_expr
  let e_sub' := rewrite.output_expr.renameMapped ext_mapping.inverse
  let (e_sub'_vars_i, e_sub'_vars_o) := e_sub'.allVars
  let int_mapping' : PortMapping String :=
    ⟨ generate_renaming fresh_prefix (e_sub'_vars_i.filter (λ x => x ∉ ext_mapping.input.keysList))
    , generate_renaming fresh_prefix (e_sub'_vars_o.filter (λ x => x ∉ ext_mapping.output.keysList))
    ⟩
  -- throw s!"{int_mapping'}"
  let e_renamed_sub' := e_sub'.renameMapped int_mapping'
  return g_lower.replace e_sub e_renamed_sub' |>.higherS fresh_prefix

structure NextNode (Ident) where
  inst : Ident
  inputPort : Ident
  portMap : PortMapping Ident
  typ : Ident
  connection : Connection Ident

def followOutput' (g : ExprHigh String) (inst output : String) : RewriteResult (NextNode String) := do
  let (pmap, _) ← ofOption (.error "instance not in modules")
    <| g.modules.find? inst
  let localOutputName ← ofOption (.error "port not in instance portmap")
    <| pmap.output.find? ⟨.top, output⟩
  let c@⟨_, localInputName⟩ ← ofOption (.error "output not in connections")
    <| g.connections.find? (λ c => c.output = localOutputName)
  let (inst, iport) ← ofOption (.error "input port not in modules")
    <| ExprHigh.findInputPort' localInputName g.modules
  ofOption (.error "instance not in modules") <| (g.modules.findEntry? inst).map (λ x => ⟨inst, iport, x.2.1, x.2.2, c⟩)

def followOutput (g : ExprHigh String) (inst output : String) : Option (NextNode String) :=
  (followOutput' g inst output).toOption

end DataflowRewriter
