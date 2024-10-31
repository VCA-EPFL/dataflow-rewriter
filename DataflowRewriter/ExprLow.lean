/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.Simp
import DataflowRewriter.Basic
import DataflowRewriter.AssocList

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
| base (map : PortMapping Ident) (typ : Ident)
| product (l r : ExprLow Ident)
| connect (o i : InternalPort Ident) (e : ExprLow Ident)
deriving Repr, Inhabited, DecidableEq

inductive NamedExprLow Ident where
| input : InternalPort Ident → Ident → NamedExprLow Ident → NamedExprLow Ident
| output : InternalPort Ident → Ident → NamedExprLow Ident → NamedExprLow Ident
| base : ExprLow Ident → NamedExprLow Ident
deriving Repr, Inhabited, DecidableEq

inductive PosTree Ident where
| here (i : InternalPort Ident)
| left (l : PosTree Ident)
| right (r : PosTree Ident)
| both (l r : PosTree Ident)

inductive SExprLow Ident where
| base (typ : Ident)
| product (l r : ExprLow Ident)
| connect (e : ExprLow Ident)

inductive NamelessPort (Ident : Type _) where
| bound (name : Nat)
| top (name : Ident)
deriving Repr, Hashable, Ord, Inhabited, DecidableEq

structure NamelessMapping (Ident) where
  input : PortMap Ident (NamelessPort Ident)
  output : PortMap Ident (NamelessPort Ident)
deriving Repr, Inhabited, DecidableEq

namespace ExprLow

variable {Ident}
variable [DecidableEq Ident]

@[drunfold] def build_mapping (map map' : PortMapping Ident) : Option (PortMapping Ident) := do
  guard <| map.input.keysList = map'.input.keysList
  guard <| map.output.keysList = map'.output.keysList
  let inputMap ← map.input.foldlM
    (λ (a : PortMap Ident (InternalPort Ident)) k v => do
      let v' ← map'.input.find? k
      return a.cons v v'
    ) ∅
  let outputMap ← map.output.foldlM
    (λ (a : PortMap Ident (InternalPort Ident)) k v => do
      let v' ← map'.output.find? k
      return a.cons v v'
    ) ∅
  return ⟨inputMap, outputMap⟩

@[drunfold] def beq : (e e' : ExprLow Ident) → Option (PortMapping Ident × PortMapping Ident)
| .base map typ, .base map' typ' => do
  guard <| typ = typ'
  build_mapping map map' |>.map (Prod.mk · ∅)
| .connect o i e, .connect o' i' e' => do
  let (map, int_map) ← e.beq e'
  let o_in_map ← map.output.find? o
  let i_in_map ← map.input.find? i
  guard <| o_in_map = o'
  guard <| i_in_map = i'
  return ( {map with input := map.input.eraseAll i, output := map.output.eraseAll o}
         , {int_map with input := int_map.input.cons i i', output := int_map.output.cons o o'}
         )
| .product e₁ e₂, .product e₁' e₂' => do
  let (map₁, int_map₁) ← e₁.beq e₁'
  let (map₂, int_map₂) ← e₂.beq e₂'
  guard <| map₁.input.disjoint_keys map₂.input
  guard <| map₁.output.disjoint_keys map₂.output
  guard <| int_map₁.output.disjoint_keys int_map₂.output
  guard <| int_map₁.output.disjoint_keys int_map₂.output
  return ( ⟨map₁.input.append map₂.input, map₁.output.append map₂.output⟩
         , ⟨int_map₁.input.append int_map₂.input, int_map₁.output.append int_map₂.output⟩
         )
| _, _ => failure

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
def renameInput (typ : Ident) (a b : InternalPort Ident) : ExprLow Ident → ExprLow Ident
| .base map typ' =>
  if typ = typ' then
    .base {map with input := map.input.erase a |>.cons a b} typ
  else
    .base map typ'
| .connect o i e =>
  let e' := e.renameInput typ a b
  if i = a then .connect o b e' else .connect o i e'
| .product e₁ e₂ =>
  .product (e₁.renameInput typ a b) (e₂.renameInput typ a b)

/--
Assume that the input is currently not mapped.
-/
@[drunfold]
def renameOutput (typ : Ident) (a b : InternalPort Ident) : ExprLow Ident → ExprLow Ident
| .base map typ' =>
  if typ = typ' then
    .base {map with output := map.output.erase a |>.cons a b} typ
  else
    .base map typ'
| .connect o i e =>
  let e' := e.renameOutput typ a b
  if o = a then .connect b i e' else .connect o i e'
| .product e₁ e₂ =>
  .product (e₁.renameOutput typ a b) (e₂.renameOutput typ a b)

@[drunfold]
def rename (typ : Ident) (p : PortMapping Ident) (e : ExprLow Ident) : ExprLow Ident :=
  p.input.foldl (λ e' k v => e'.renameInput typ k v) e
  |> p.output.foldl (λ e' k v => e'.renameOutput typ k v)

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
