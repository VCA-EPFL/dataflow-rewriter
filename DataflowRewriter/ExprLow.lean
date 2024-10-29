/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.Simp
import DataflowRewriter.Basic

namespace DataflowRewriter

/--
ExprLow is an inductive definition of a circuit, inspired by a definition by
Tony Law [?].  The main difference is th edadition of input and output
constructors that essentially just rename a port to a top-level IO port.

An alternative definition of IO ports was considered, in that they could just be
a `base` module.  This has advantages because it makes the definition more
uniform, however, when building a `Module` from an `ExprLow`, one would have
additional state to be able to communicate from an input to the input for the
module.
-/
inductive ExprLow Ident where
| base : PortMapping Ident → Ident → ExprLow Ident
| product : ExprLow Ident → ExprLow Ident → ExprLow Ident
| connect : InternalPort Ident → InternalPort Ident → ExprLow Ident → ExprLow Ident
deriving Repr, Inhabited, DecidableEq

inductive NamedExprLow Ident where
| input : InternalPort Ident → Ident → NamedExprLow Ident → NamedExprLow Ident
| output : InternalPort Ident → Ident → NamedExprLow Ident → NamedExprLow Ident
| base : ExprLow Ident → NamedExprLow Ident
deriving Repr, Inhabited, DecidableEq

namespace ExprLow

variable {Ident}
variable [DecidableEq Ident]

@[drunfold] def modify (i i' : Ident) : ExprLow Ident → ExprLow Ident
| .base inst typ => if typ = i then .base inst i' else .base inst typ
| .connect x y e' => modify i i' e' |> .connect x y
| .product e₁ e₂ =>
  let e₁' := e₁.modify i i'
  let e₂' := e₂.modify i i'
  .product e₁' e₂'

@[drunfold] def replace (e e_sub e_new : ExprLow Ident) : ExprLow Ident :=
  if e = e_sub then e_new else
  match e with
  | .base inst typ => e
  | .connect x y e_sub' => .connect x y (e_sub'.replace e_sub e_new)
  | .product e_sub₁ e_sub₂ =>
    .product (e_sub₁.replace e_sub e_new) (e_sub₂.replace e_sub e_new)

@[drunfold]
def abstract (e e_sub : ExprLow Ident) (i_inst : PortMapping Ident) (i_typ : Ident) : ExprLow Ident :=
  .base i_inst i_typ |> e.replace e_sub

@[drunfold]
def concretise (e e_sub : ExprLow Ident) (i_inst : PortMapping Ident) (i_typ : Ident) : ExprLow Ident :=
  .base i_inst i_typ |> (e.replace · e_sub)

/--
Assume that the input is currently not mapped.
-/
@[drunfold]
def renameUnmappedInput (typ : Ident) (a b : InternalPort Ident) : ExprLow Ident → ExprLow Ident
| .base map typ' =>
  if typ = typ' && (map.input.find? a).isNone then
    .base {map with input := map.input |>.cons a b} typ
  else
    .base map typ'
| .connect o i e =>
  let e' := e.renameUnmappedInput typ a b
  if i = a then .connect o b e' else .connect o i e'
| .product e₁ e₂ =>
  .product (e₁.renameUnmappedInput typ a b) (e₂.renameUnmappedInput typ a b)

/--
Assume that the input is mapped.
-/
@[drunfold]
def renameMappedInput (a b : InternalPort Ident) : ExprLow Ident → ExprLow Ident
| .base map typ =>
  .base {map with input := map.input.mapVal (λ k v => if v = a then b else v)} typ
| .connect o i e =>
  let e' := e.renameMappedInput a b
  if i = a then .connect o b e' else .connect o i e'
| .product e₁ e₂ =>
  .product (e₁.renameMappedInput a b) (e₂.renameMappedInput a b)

/--
Assume that the output is currently not mapped.
-/
@[drunfold]
def renameUnmappedOutput (typ : Ident) (a b : InternalPort Ident) : ExprLow Ident → ExprLow Ident
| .base map typ' =>
  if typ = typ' && (map.output.find? a).isNone then
    .base {map with output := map.output |>.cons a b} typ
  else
    .base map typ'
| .connect o i e =>
  let e' := e.renameUnmappedOutput typ a b
  if i = a then .connect o b e' else .connect o i e'
| .product e₁ e₂ =>
  .product (e₁.renameUnmappedOutput typ a b) (e₂.renameUnmappedOutput typ a b)

/--
Assume that the output is mapped.
-/
@[drunfold]
def renameMappedOutput (a b : InternalPort Ident) : ExprLow Ident → ExprLow Ident
| .base map typ =>
  .base {map with output := map.output.mapVal (λ k v => if v = a then b else v)} typ
| .connect o i e =>
  let e' := e.renameMappedOutput a b
  if i = a then .connect o b e' else .connect o i e'
| .product e₁ e₂ =>
  .product (e₁.renameMappedOutput a b) (e₂.renameMappedOutput a b)

@[drunfold]
def rename (typ : Ident) (p : PortMapping Ident) (e : ExprLow Ident) : ExprLow Ident :=
  p.input.foldl (λ e' k v => e'.renameUnmappedInput typ k v) e
  |> p.output.foldl (λ e' k v => e'.renameUnmappedOutput typ k v)

def isExternalInputPort' (int : IdentMap Ident (Interface Ident)) (p : InternalPort Ident) : ExprLow Ident → Bool
| .base map typ =>
  map.input.any (λ k v => v = p && match int.find? typ with | .some int => k ∈ int.input | .none => false)
  || (match int.find? typ with | .some int => p ∈ int.input && !map.input.contains p | .none => false)
| .connect o i e =>
  if i = p then false else e.isExternalInputPort' int p
| .product e₁ e₂ =>
  e₁.isExternalInputPort' int p || e₂.isExternalInputPort' int p

def isInternalInputPort' (int : IdentMap Ident (Interface Ident)) (p : InternalPort Ident) : ExprLow Ident → Bool
| .base map typ =>
  map.input.any (λ k v => v = p) || (match int.find? typ with | .some int => p ∈ int.input && !map.input.contains p | .none => true)
| .connect o i e =>
  if i = p then true else e.isInternalInputPort' int p
| .product e₁ e₂ =>
  e₁.isInternalInputPort' int p && e₂.isInternalInputPort' int p

def isInternalOutputPort' (int : IdentMap Ident (Interface Ident)) (p : InternalPort Ident) : ExprLow Ident → Bool
| .base map typ =>
  map.output.any (λ k v => v = p) || (match int.find? typ with | .some int => p ∈ int.output && !map.output.contains p | .none => true)
| .connect o i e =>
  if o = p then true else e.isInternalOutputPort' int p
| .product e₁ e₂ =>
  e₁.isInternalOutputPort' int p && e₂.isInternalOutputPort' int p

@[drunfold]
def calc_mapping : ExprLow Ident → PortMapping Ident
| .base inst typ => inst
| .connect _x _y e => e.calc_mapping
| .product e₁ e₂ => e₁.calc_mapping ++ e₂.calc_mapping

def all (P : Ident → Bool) : ExprLow Ident → Bool
| base f typ => P typ
| connect o i e => e.all P
| product e₁ e₂ => e₁.all P && e₂.all P

def any (P : Ident → Bool) : ExprLow Ident → Bool
| base f typ => P typ
| connect o i e => e.any P
| product e₁ e₂ => e₁.any P || e₂.any P

def excludes (ident : Ident) : ExprLow Ident → Bool := all (· ≠ ident)

end ExprLow
end DataflowRewriter
