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

structure Connection (Ident : Type _) where
  output : InternalPort Ident
  input  : InternalPort Ident
deriving Repr, Hashable, DecidableEq, Ord, Inhabited

namespace ExprLow

variable {Ident}
variable [DecidableEq Ident]

def ofOption {α ε} (e : ε) : Option α → Except ε α
| some o => .ok o
| none => .error e

@[drunfold] def build_mapping [Repr Ident] (map map' : PortMapping Ident) : Except String (PortMapping Ident) := do
  unless map.input.keysList.isPerm map'.input.keysList do
    throw s!"build_mapping error: input {map.input.keysList} is not a permutation of {map'.input.keysList}"
  unless map.output.keysList.isPerm map'.output.keysList do
    throw s!"build_mapping error: output {map.output.keysList} is not a permutation of {map'.output.keysList}"
  let inputMap ← map.input.foldlM
    (λ (a : PortMap Ident (InternalPort Ident)) k v => do
      let v' ← ofOption s!"build_mapping error: input: could not find {k} in {map'}" <| map'.input.find? k
      return a.cons v v'
    ) ∅
  let outputMap ← map.output.foldlM
    (λ (a : PortMap Ident (InternalPort Ident)) k v => do
      let v' ← ofOption s!"build_mapping error: output could not find {k} in {map'}" <| map'.output.find? k
      return a.cons v v'
    ) ∅
  return ⟨inputMap, outputMap⟩

@[drunfold] def beq [Repr Ident] : (e e' : ExprLow Ident) → Except String (PortMapping Ident × PortMapping Ident)
| .base map typ, .base map' typ' => do
  unless typ = typ' do throw s!"beq error: types are not equal: {repr typ} vs {repr typ'}"
  build_mapping map map' |>.map (Prod.mk · ∅)
| .connect o i e, .connect o' i' e' => do
  let (map, int_map) ← e.beq e'
  let o_in_map ← ofOption "beq error: could not find output in map" <| map.output.find? o
  let i_in_map ← ofOption "beq error: could not find input in map" <| map.input.find? i
  unless o_in_map = o' do throw s!"beq error: o_in_map ({o_in_map}) ≠ o' ({o'})"
  unless i_in_map = i' do throw s!"beq error: i_in_map ({i_in_map}) ≠ i' ({i'})"
  return ( {map with input := map.input.eraseAll i, output := map.output.eraseAll o}
         , {int_map with input := int_map.input.cons i i', output := int_map.output.cons o o'}
         )
| .product e₁ e₂, .product e₁' e₂' => do
  let (map₁, int_map₁) ← e₁.beq e₁'
  let (map₂, int_map₂) ← e₂.beq e₂'
  unless map₁.input.disjoint_keys map₂.input do throw "beq error: map₁.input not disjoint from map₂.input"
  unless map₁.output.disjoint_keys map₂.output do throw "beq error: map₁.output not disjoint from map₂.output"
  unless int_map₁.input.disjoint_keys int_map₂.input do throw "beq error: int_map₁.input not disjoint from int_map₂.input"
  unless int_map₁.output.disjoint_keys int_map₂.output do do throw "beq error: int_map₁.output not disjoint from int_map₂.output"
  return ( ⟨map₁.input.append map₂.input, map₁.output.append map₂.output⟩
         , ⟨int_map₁.input.append int_map₂.input, int_map₁.output.append int_map₂.output⟩
         )
| _, _ => throw "beq error: expressions are structurally not similar"

@[drunfold] def weak_beq [Repr Ident] : (e e' : ExprLow Ident) → Except String (PortMapping Ident × PortMapping Ident)
| .base map typ, .base map' typ' => do
  unless typ = typ' do throw s!"beq error: types are not equal: {repr typ} vs {repr typ'}"
  build_mapping map map' |>.map (Prod.mk · ∅)
| .connect o i e, .connect o' i' e' => do
  let (map, int_map) ← e.weak_beq e'
  let o_in_map ← ofOption "beq error: could not find output in map" <| map.output.find? o
  let i_in_map ← ofOption "beq error: could not find input in map" <| map.input.find? i
  -- unless o_in_map = o' do throw s!"beq error: o_in_map ({o_in_map}) ≠ o' ({o'})"
  -- unless i_in_map = i' do throw s!"beq error: i_in_map ({i_in_map}) ≠ i' ({i'})"
  return ( {map with input := map.input.eraseAll i, output := map.output.eraseAll o}
         , {int_map with input := int_map.input.cons i i_in_map, output := int_map.output.cons o o_in_map}
         )
| .product e₁ e₂, .product e₁' e₂' => do
  let (map₁, int_map₁) ← e₁.weak_beq e₁'
  let (map₂, int_map₂) ← e₂.weak_beq e₂'
  unless map₁.input.disjoint_keys map₂.input do throw "beq error: map₁.input not disjoint from map₂.input"
  unless map₁.output.disjoint_keys map₂.output do throw "beq error: map₁.output not disjoint from map₂.output"
  unless int_map₁.input.disjoint_keys int_map₂.input do throw "beq error: int_map₁.input not disjoint from int_map₂.input"
  unless int_map₁.output.disjoint_keys int_map₂.output do do throw "beq error: int_map₁.output not disjoint from int_map₂.output"
  return ( ⟨map₁.input.append map₂.input, map₁.output.append map₂.output⟩
         , ⟨int_map₁.input.append int_map₂.input, int_map₁.output.append int_map₂.output⟩
         )
| _, _ => throw "beq error: expressions are structurally not similar"

@[drunfold] def build_interface : ExprLow Ident → Interface Ident
| .base map typ => map.toInterface'
| .connect o i e =>
  let int := e.build_interface
  ⟨int.input.erase i, int.output.erase o⟩
| product e₁ e₂ =>
  let int₁ := e₁.build_interface
  let int₂ := e₂.build_interface
  ⟨int₁.input ++ int₂.input, int₁.output ++ int₂.output⟩

@[drunfold] def allVars : ExprLow Ident → (List (InternalPort Ident) × List (InternalPort Ident))
| .base map typ =>
  (map.input.toList.map Prod.snd, map.output.toList.map Prod.snd)
| .connect o i e => e.allVars
| .product e₁ e₂ =>
  let (e₁i, e₁o) := e₁.allVars
  let (e₂i, e₂o) := e₂.allVars
  (e₁i ++ e₂i, e₁o ++ e₂o)

@[drunfold] def modify (i i' : Ident) : ExprLow Ident → ExprLow Ident
| .base inst typ => if typ = i then .base inst i' else .base inst typ
| .connect x y e' => modify i i' e' |> .connect x y
| .product e₁ e₂ =>
  let e₁' := e₁.modify i i'
  let e₂' := e₂.modify i i'
  .product e₁' e₂'

/--
Check that two expressions are equal, assuming that the port assignments are
fully specified and therefore symmetric in both expressions.
-/
@[drunfold] def check_eq : ExprLow Ident → ExprLow Ident → Bool
| .base inst typ, .base inst' typ' =>
  -- let inst_i := inst.input.filterId
  -- let inst_o := inst.output.filterId
  -- let inst'_i := inst'.input.filterId
  -- let inst'_o := inst'.output.filterId
  typ = typ'
  ∧ inst'.input.EqExt inst.input ∧ inst'.output.EqExt inst.output
  ∧ inst'.input.keysList.Nodup ∧ inst.output.keysList.Nodup
  ∧ inst'.output.keysList.Nodup ∧ inst.input.keysList.Nodup
  -- ∧ inst'_i.EqExt inst_i ∧ inst'_o.EqExt inst_o
  -- ∧ inst'_i.keysList.Nodup ∧ inst_i.keysList.Nodup
  -- ∧ inst'_o.keysList.Nodup ∧ inst_o.keysList.Nodup
| .connect o i e, .connect o' i' e' => o = o' ∧ i = i' ∧ e.check_eq e'
| .product e₁ e₂, .product e₁' e₂' => e₁.check_eq e₁' ∧ e₂.check_eq e₂'
| _, _ => false

@[drunfold] def replace (e e_sub e_new : ExprLow Ident) : ExprLow Ident :=
  if e.check_eq e_sub then e_new else
  match e with
  | .base inst typ => e
  | .connect x y e_sub' => .connect x y (e_sub'.replace e_sub e_new)
  | .product e_sub₁ e_sub₂ =>
    .product (e_sub₁.replace e_sub e_new) (e_sub₂.replace e_sub e_new)

@[drunfold] def force_replace (e e_sub e_new : ExprLow Ident) : (ExprLow Ident × Bool) :=
  if e.check_eq e_sub then (e_new, true) else
  match e with
  | .base inst typ => (e, false)
  | .connect x y e_sub' =>
    let rep := e_sub'.force_replace e_sub e_new
    (.connect x y rep.1, rep.2)
  | .product e_sub₁ e_sub₂ =>
    let e_sub₁_rep := e_sub₁.force_replace e_sub e_new
    let e_sub₂_rep := e_sub₂.force_replace e_sub e_new
    (.product e_sub₁_rep.1 e_sub₂_rep.1, e_sub₁_rep.2 || e_sub₂_rep.2)

@[drunfold]
def abstract (e e_sub : ExprLow Ident) (i_inst : PortMapping Ident) (i_typ : Ident) : ExprLow Ident :=
  .base i_inst i_typ |> e.replace e_sub

@[drunfold]
def force_abstract (e e_sub : ExprLow Ident) (i_inst : PortMapping Ident) (i_typ : Ident) : ExprLow Ident × Bool :=
  .base i_inst i_typ |> e.force_replace e_sub

@[drunfold]
def concretise (e e_sub : ExprLow Ident) (i_inst : PortMapping Ident) (i_typ : Ident) : ExprLow Ident :=
  .base i_inst i_typ |> (e.replace · e_sub)

@[drunfold]
def force_concretise (e e_sub : ExprLow Ident) (i_inst : PortMapping Ident) (i_typ : Ident) : ExprLow Ident × Bool :=
  .base i_inst i_typ |> (e.force_replace · e_sub)

@[drunfold]
def normalisedNamesMap' (pref : String) (count : Nat) : ExprLow String → (PortMapping String × Nat)
| .base port typ' =>
  let p := port.inverse.mapPairs
    (λ | ⟨.top, n⟩, v => ⟨.top, n⟩
       | ⟨.internal _, _⟩, ⟨_, n⟩ => ⟨.internal <| pref ++ toString count, n⟩)
    |>.filter (λ | ⟨.top, _⟩, _ => false | _, _ => true)
  (p, count + 1)
| .connect _ _ e => normalisedNamesMap' pref count e
| .product e₁ e₂ =>
  let (p₁, count₁) := normalisedNamesMap' pref count e₁
  let (p₂, count₂) := normalisedNamesMap' pref count₁ e₂
  (p₁.append p₂, count₂)

@[drunfold]
def normalisedNamesMap (pref : String) (e : ExprLow String) : PortMapping String :=
  normalisedNamesMap' pref 0 e |>.fst

def findBase (typ : Ident) : ExprLow Ident → Option (PortMapping Ident)
| .base port typ' => if typ = typ' then some port else none
| .connect o i e => e.findBase typ
| .product e₁ e₂ =>
  match e₁.findBase typ with
  | some port => port
  | none => e₂.findBase typ

def mapInputPorts (f : InternalPort Ident → InternalPort Ident) : ExprLow Ident → ExprLow Ident
| .base map typ' => .base ⟨map.input.mapVal (λ _ => f), map.output⟩ typ'
| .connect o i e => e.mapInputPorts f  |> .connect o (f i)
| .product e₁ e₂ => .product (e₁.mapInputPorts f) (e₂.mapInputPorts f)

def mapOutputPorts (f : InternalPort Ident → InternalPort Ident) : ExprLow Ident → ExprLow Ident
| .base map typ' => .base ⟨map.input, map.output.mapVal (λ _ => f)⟩ typ'
| .connect o i e => e.mapOutputPorts f  |> .connect (f o) i
| .product e₁ e₂ => .product (e₁.mapOutputPorts f) (e₂.mapOutputPorts f)

def mapPorts2 (f g : InternalPort Ident → InternalPort Ident) (e : ExprLow Ident) : ExprLow Ident :=
  e.mapInputPorts f |>.mapOutputPorts g

def invertible {α} [DecidableEq α] (p : Batteries.AssocList α α) : Bool :=
  p.keysList.inter p.inverse.keysList = ∅ ∧ p.keysList.Nodup ∧ p.inverse.keysList.Nodup

def renamePorts (m : ExprLow Ident) (p : PortMapping Ident) : ExprLow Ident :=
  m.mapPorts2 p.input.bijectivePortRenaming p.output.bijectivePortRenaming

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
  if o = a then .connect b i e' else .connect o i e'
| .product e₁ e₂ =>
  .product (e₁.renameMappedOutput a b) (e₂.renameMappedOutput a b)

@[drunfold]
def rename (typ : Ident) (p : PortMapping Ident) (e : ExprLow Ident) : ExprLow Ident :=
  p.input.foldl (λ e' k v => e'.renameUnmappedInput typ k v) e
  |> p.output.foldl (λ e' k v => e'.renameUnmappedOutput typ k v)

@[drunfold]
def renameMapped (p : PortMapping Ident) (e : ExprLow Ident) : ExprLow Ident :=
  p.input.foldl (λ e' k v => e'.renameMappedInput k v) e
  |> p.output.foldl (λ e' k v => e'.renameMappedOutput k v)

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

def _root_.List.eraseAll {α} [DecidableEq α] : List α → α → List α
| [],    _ => []
| a::as, b => match a == b with
  | true  => List.eraseAll as b
  | false => a :: List.eraseAll as b

def findAllInputs : ExprLow Ident → List (InternalPort Ident)
| .base inst _typ => inst.input.valsList
| .product e₁ e₂ => e₁.findAllInputs ++ e₂.findAllInputs
| .connect o i e => e.findAllInputs.eraseAll i

def findAllOutputs : ExprLow Ident → List (InternalPort Ident)
| .base inst _typ => inst.input.valsList
| .product e₁ e₂ => e₁.findAllInputs ++ e₂.findAllInputs
| .connect o i e => e.findAllInputs.eraseAll i

def ensureIOUnmodified (p : PortMapping Ident) (e : ExprLow Ident) : Bool :=
  e.findAllInputs.all (λ x => (p.input.find? x).isNone)
  ∧ e.findAllOutputs.all (λ x => (p.output.find? x).isNone)

/--
Find input and find output imply that build_module will contain that key
-/
def findInput (i : InternalPort Ident) : ExprLow Ident → Bool
| .base inst _typ => inst.input.any (λ _ a => a = i)
| .product e₁ e₂ => findInput i e₁ ∨ findInput i e₂
| .connect _o i' e => i' ≠ i ∧ findInput i e

def findOutput (o : InternalPort Ident) : ExprLow Ident → Bool
| .base inst _typ => inst.output.any (λ _ a => a = o)
| .product e₁ e₂ => findOutput o e₁ ∨ findOutput o e₂
| .connect o' _i e => o' ≠ o ∧ findOutput o e

def fix_point (f : ExprLow Ident → ExprLow Ident) (e : ExprLow Ident): Nat → ExprLow Ident
| 0 => e
| n+1 => let e' := f e; if e' = e then e else fix_point f e' n

def fix_point_opt (f : ExprLow Ident → Option (ExprLow Ident)) (e : ExprLow Ident): Nat → ExprLow Ident
| 0 => e
| n+1 =>
  match f e with
  | .some e' => fix_point_opt f e' n
  | .none => e

def inst_disjoint (inst inst' : PortMapping Ident) : Bool :=
  inst'.input.disjoint_vals inst.input ∧ inst'.output.disjoint_vals inst.output

def comm_connection'_ (conn : Connection Ident) : ExprLow Ident → Option (ExprLow Ident)
| .connect o i e =>
  if o = conn.output ∧ i = conn.input then
    match e with
    | .connect o' i' e' =>
      if o ≠ o' ∧ i ≠ i' then
        .some (.connect o' i' (.connect o i e'))
      else .none
    | .product e₁ e₂ =>
      let a := e₁.findInput i
      let b := e₁.findOutput o
      if a ∧ b then
        -- .product (comm_connection' conn <| .connect o i e₁) e₂
        -- We actually don't want to commute (assuming we are left associative)
        .none
      else if ¬ a ∧ ¬ b ∧ e₂.findInput i ∧ e₂.findOutput o then
        .some (.product e₁ (.connect o i e₂))
      else .none
    | _ => .none
  else .connect o i <$> comm_connection'_ conn e
| .product e₁ e₂ =>
  match (comm_connection'_ conn e₁), (comm_connection'_ conn e₂) with
  | .some e₁, .some e₂ | .some e₁, .none | .none, .some e₂ => .some <| .product e₁ e₂
  | .none, .none => .none
| e => .none

def comm_connection' (conn : Connection Ident) e := fix_point_opt (comm_connection'_ conn) e 10000

def comm_connection_ (conn : Connection Ident) : ExprLow Ident → ExprLow Ident
| orig@(.connect o i e) =>
  if o = conn.output ∧ i = conn.input then
    match e with
    | .connect o' i' e' =>
      if o ≠ o' ∧ i ≠ i' then
        .connect o' i' (.connect o i e')
      else orig
    | _ => orig
  else .connect o i <| comm_connection_ conn e
| .product e₁ e₂ =>
  .product (comm_connection_ conn e₁) (comm_connection_ conn e₂)
| e => e

def comm_connection (conn : Connection Ident) e := fix_point (comm_connection_ conn) e 10000

/- Assuming a left-associative expression. -/
def comm_base_ {Ident} [DecidableEq Ident] (binst : PortMapping Ident) (btyp : Ident) : ExprLow Ident → Option (ExprLow Ident)
| .product e₁ e₂ =>
  if e₁ = .base binst btyp then
    match e₂ with
    | .product (.base binst' btyp') e₂' =>
      if inst_disjoint binst' binst then
        .some <| .product (.base binst' btyp') (.product e₁ e₂')
      else .none
    | .connect o i e =>
      if o ∉ binst.output.valsList ∧ i ∉ binst.input.valsList then
        .some <| .connect o i (.product e₁ e)
      else .none
    | .base binst' btyp' =>
      if inst_disjoint binst' binst then .some <| .product e₂ e₁ else .none
    | _ => .none
  else .product e₁ <$> comm_base_ binst btyp e₂
| .connect o i e => .connect o i <$> comm_base_ binst btyp e
| e => .none

def comm_base (binst : PortMapping Ident) (btyp : Ident) e := fix_point_opt (comm_base_ binst btyp) e 10000

def comm_connections' {Ident} [DecidableEq Ident] (conn : List (Connection Ident)) (e : ExprLow Ident): ExprLow Ident :=
  conn.foldr comm_connection' e

def comm_connections {Ident} [DecidableEq Ident] (conn : List (Connection Ident)) (e : ExprLow Ident): ExprLow Ident :=
  conn.foldr comm_connection e

def comm_bases {Ident} [DecidableEq Ident] (bases : List (PortMapping Ident × Ident)) (e : ExprLow Ident): ExprLow Ident :=
  bases.foldr (Function.uncurry ExprLow.comm_base) e

end ExprLow
end DataflowRewriter
