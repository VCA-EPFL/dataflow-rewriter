/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Lean
import DataflowRewriter.ExprLow

namespace DataflowRewriter

/--
Graph description of a cicruit.  Note that currently one cannot describe an
input that connects directly to the output.  Instead, these always have to pass
by an internal module.
-/
structure ExprHigh (Ident : Type _) where
  modules     : IdentMap Ident (PortMapping Ident × Ident)
  connections : List (Connection Ident)
deriving Repr, DecidableEq, Inhabited

structure NamedExprHigh (Ident : Type _) where
  graph       : ExprHigh Ident
  inPorts     : IdentMap Ident (InternalPort Ident)
  outPorts    : IdentMap Ident (InternalPort Ident)

structure NextNode (Ident) where
  inst : Ident
  inputPort : Ident
  outputPort : Ident
  portMap : PortMapping Ident
  typ : Ident
  connection : Connection Ident
deriving Repr, Inhabited

namespace ExprHigh

universe i
variable {Ident : Type i}
variable [DecidableEq Ident]

def findInputPort (p : InternalPort Ident) (i : IdentMap Ident (PortMapping Ident × Ident)) : Option Ident :=
  i.foldl (λ a k v =>
      match a with | some a' => a | none => do
        let _ ← if (v.fst.input.filter (λ k' v' => p = v')).length > 0 then pure PUnit.unit else failure
        return k
    ) none

def findInputPort' (p : InternalPort Ident) (i : IdentMap Ident (PortMapping Ident × Ident)) : Option (Ident × Ident) :=
  i.foldl (λ a k v =>
      match a with | some a' => a | none => do
        let l ← v.fst.input.findEntryP? (λ k' v' => p = v')
        return (k, l.fst.name)
    ) none

def findOutputPort (p : InternalPort Ident) (i : IdentMap Ident (PortMapping Ident × Ident)) : Option Ident :=
  i.foldl (λ a k v =>
      match a with | some a' => a | none => do
        let _ ← if (v.fst.output.filter (λ k' v' => p = v')).length > 0 then pure PUnit.unit else failure
        return k
    ) none

def findOutputPort' (p : InternalPort Ident) (i : IdentMap Ident (PortMapping Ident × Ident)) : Option (Ident × Ident) :=
  i.foldl (λ a k v =>
      match a with | some a' => a | none => do
        let l ← v.fst.output.findEntryP? (λ k' v' => p = v')
        return (k, l.fst.name)
    ) none

def inputNodes (g : ExprHigh Ident) : List Ident :=
  g.modules.foldl (λ inodes k v =>
      if v.fst.input.any (λ _ k => k.inst.isTop)
      then k :: inodes
      else inodes
    ) ∅

def outputNodes (g : ExprHigh Ident) : List Ident :=
  g.modules.foldl (λ inodes k v =>
      if v.fst.output.any (λ _ k => k.inst.isTop)
      then k :: inodes
      else inodes
    ) ∅

def normaliseModules (g : ExprHigh Ident) : Option (ExprHigh Ident) := do
  let newModules ← g.modules.foldlM (λ nm k v => do
      let inp := v.fst.input.mapVal (
          λ | ⟨_, portName⟩, ⟨.internal inst, name⟩ =>
              ⟨.internal k, portName⟩
            | _, v => v
        )
      let out := v.fst.output.mapVal (
          λ | ⟨_, portName⟩, ⟨.internal inst, name⟩ =>
              ⟨.internal k, portName⟩
            | _, v => v
        )
      return nm.cons k (⟨inp, out⟩, v.snd)
    ) ∅
  return {g with modules := newModules}

def normaliseNames (g : ExprHigh Ident) : Option (ExprHigh Ident) := do
  let newConnections ← g.connections.mapM (λ
    | ⟨i₁@⟨.internal _, n₁⟩, i₂@⟨.internal _, n₂⟩⟩ => do
      let (outInst, outInstName) ← findOutputPort' i₁ g.modules
      let (inInst, inInstName) ← findInputPort' i₂ g.modules
      return Connection.mk ⟨.internal outInst, outInstName⟩ ⟨.internal inInst, inInstName⟩
    | ⟨i₁@⟨.top, n₁⟩, i₂@⟨.internal _, n₂⟩⟩ => do
      let (inInst, inInstName) ← findInputPort' i₂ g.modules
      return Connection.mk ⟨.top, n₁⟩ ⟨.internal inInst, inInstName⟩
    | ⟨i₁@⟨.internal _, n₁⟩, i₂@⟨.top, n₂⟩⟩ => do
      let (outInst, outInstName) ← findOutputPort' i₁ g.modules
      return Connection.mk ⟨.internal outInst, outInstName⟩ ⟨.top, n₂⟩
    | c => pure c
    )
  {g with connections := newConnections}.normaliseModules

instance (Ident) [DecidableEq Ident] [Repr Ident] [ToString Ident] : ToString (ExprHigh Ident) where
  toString a :=
    -- let instances :=
    --   a.modules.foldl (λ s inst mod => s ++ s!"\n {inst} [mod = \"{mod}\"];") ""
    match a.normaliseNames with
    | some a =>
      let (io_decl, io_conn) := a.modules.foldl (λ (sdecl, sio) inst (pmap, typ) =>
        let sdecl := (pmap.input ++ pmap.output).foldl (λ sdecl k v =>
          if v.inst.isTop
          then sdecl ++ s!"\n  {v.name} [type = \"io\", label = \"{v.name}: io\"];"
          else sdecl) sdecl
        let sio := pmap.input.foldl (λ io_conn k v =>
          if v.inst.isTop
          then io_conn ++ s!"\n  {v.name} -> {inst} [to = \"{k.name}\", headlabel = \"{k.name}\"];"
          else io_conn) sio
        let sio := pmap.output.foldl (λ io_conn k v =>
          if v.inst.isTop
          then io_conn ++ s!"\n  {inst} -> {v.name} [from = \"{k.name}\", taillabel = \"{k.name}\"];"
          else io_conn) sio
        (sdecl, sio)
      ) ("", "")
      let modules :=
        a.modules.foldl
          (λ s k v =>
            s ++ s!"  {k} [type = \"{v.snd}\", label = \"{k}: {v.snd}\"];\n"
            ) ""
      let connections :=
        a.connections.foldl
          (λ s => λ | ⟨ oport, iport ⟩ =>
                      s ++ s!"\n  {oport.inst} -> {iport.inst} "
                        ++ s!"[from = \"{oport.name}\","
                        ++ s!" to = \"{iport.name}\","
                        ++ s!" taillabel = \"{oport.name}\","
                        ++ s!" headlabel = \"{iport.name}\","
                        ++ "];") ""
      s!"digraph \{
{io_decl}
{modules}
{io_conn}
{connections}
}"
    | none => repr a |>.pretty

def invert (g : ExprHigh Ident) : ExprHigh Ident :=
  let mods := g.modules.mapVal
    (λ k v => ({v.fst with input := v.fst.output, output := v.fst.input}, v.snd))
  let conns := g.connections.map (λ a => ⟨a.input, a.output⟩)
  ⟨mods, conns⟩

@[inline] def uncurry {α β γ} (f : α → β → γ) (v : α × β): γ :=
  f v.fst v.snd

@[drunfold] def lower' (el : ExprLow Ident) (e : ExprHigh Ident) : ExprLow Ident :=
  let prod_expr :=
    e.modules.toList.foldl (λ expr val =>
        -- return .product (.base (int.toPortMapping val.1) val.2) expr)
        .product (uncurry .base val.snd) expr) el
  e.connections.foldl (λ expr conn => .connect conn expr) prod_expr

@[drunfold] def lower (e : ExprHigh Ident) : Option (ExprLow Ident) :=
  match e.modules.toList with
  | x :: xs => some <| {e with modules := xs.toAssocList}.lower' (uncurry .base x.snd)
  | _ => none

end ExprHigh

class FreshIdent (Ident : Type _) where
  next : Nat → Ident

instance : FreshIdent String where
  next n := "type" ++ toString n

instance : FreshIdent Nat where
  next := id

namespace ExprLow

variable {Ident : Type _}
variable [DecidableEq Ident]
variable [Inhabited Ident]

def higher' [FreshIdent Ident] (fresh : Nat) : ExprLow Ident → (ExprHigh Ident × Nat)
| .base a b =>
  (ExprHigh.mk [(a.ofPortMapping.getD (FreshIdent.next fresh), (a, b))].toAssocList ∅, fresh + 1)
| .connect c e =>
  let (e', fresh') := e.higher' fresh
  ({ e' with connections := e'.connections.cons c }, fresh')
| .product e₁ e₂ =>
  let (e₁', fresh₁) := e₁.higher' fresh
  let (e₂', fresh₂) := e₂.higher' fresh₁
  (⟨ e₁'.1.append e₂'.1, e₁'.2.append e₂'.2 ⟩, fresh₂)

def higher [Inhabited Ident] [FreshIdent Ident] (e: ExprLow Ident) : ExprHigh Ident :=
  e.higher' default |>.fst

def higherS' (fresh : Nat) (fresh_prefix : String) : ExprLow String → (ExprHigh String × Nat)
| .base a b =>
  (ExprHigh.mk [(fresh_prefix ++ toString fresh, (a, b))].toAssocList ∅, fresh + 1)
| .connect c e =>
  let (e', fresh') := e.higherS' fresh fresh_prefix
  ( {e' with connections := e'.connections.cons c }, fresh')
| .product e₁ e₂ =>
  let (e₁', fresh₁) := e₁.higherS' fresh fresh_prefix
  let (e₂', fresh₂) := e₂.higherS' fresh₁ fresh_prefix
  (⟨ e₁'.1.append e₂'.1, e₁'.2.append e₂'.2 ⟩, fresh₂)

def higherS (fresh_prefix : String) (e: ExprLow String) : ExprHigh String :=
  e.higherS' 0 fresh_prefix |>.fst

def _root_.DataflowRewriter.PortMap.getInstanceName' (a : PortMap Ident (InternalPort Ident)) (i : Option Ident) : Option Ident :=
  match a with
  | .cons _ ⟨.top, n⟩ xs => getInstanceName' xs (match i with | .some _ => i | _ => .some n)
  | .cons _ ⟨.internal a, _⟩ _ => .some a
  | .nil => i

def _root_.DataflowRewriter.PortMap.getInstanceName (a : PortMap Ident (InternalPort Ident)) : Option Ident := a.getInstanceName' .none

def _root_.DataflowRewriter.PortMapping.getInstanceName (a : PortMapping Ident) : Option Ident :=
  a.output.getInstanceName' a.input.getInstanceName

def higherSS : ExprLow String → Option (ExprHigh String)
| .base a b => do
  return ExprHigh.mk [(← a.getInstanceName, (a, b))].toAssocList ∅
| .connect c e => do
  let e' ← e.higherSS
  return { e' with connections := e'.connections.cons c }
| .product e₁ e₂ => do
  let e₁' ← e₁.higherSS
  let e₂' ← e₂.higherSS
  return ⟨ e₁'.1.append e₂'.1, e₁'.2.append e₂'.2 ⟩

end ExprLow

namespace ExprHigh

variable {Ident : Type _}
variable [DecidableEq Ident]
variable [Inhabited Ident]

@[drunfold] def reorder (g : ExprHigh Ident) (sub : List Ident) : ExprHigh Ident :=
  let m1 := g.modules.filter (λ k v => k ∈ sub)
  let m2 := g.modules.filter (λ k v => k ∉ sub)
  {g with modules := m1 ++ m2}

@[drunfold] def extract (g : ExprHigh Ident) (sub : List Ident)
    : Option (ExprHigh Ident × ExprHigh Ident) := do
  let modules : IdentMap Ident (PortMapping Ident × Ident) ← sub.foldlM (λ a b => do
      let l ← g.modules.find? b
      return a.cons b l
    ) ∅
  let mergedPortMapping : PortMapping Ident :=
    modules.foldl (λ pmap k v => pmap.append v.fst) ∅
  let connections := g.connections.partition
    (λ x => (mergedPortMapping.output.findEntryP? (λ _ k => k = x.output)).isSome
            && (mergedPortMapping.input.findEntryP? (λ _ k => k = x.input)).isSome)
  return (⟨ modules.toList.reverse.toAssocList, connections.fst ⟩, ⟨ g.modules.filter (λ k _ => k ∉ sub), connections.snd ⟩)

-- @[drunfold] def replace [FreshIdent Ident]
--   (g : ExprHigh Ident) (sub : List Ident) (g' : ExprHigh Ident)
--   : Option (ExprHigh Ident) := do
--   let e_sub ← (← g.extract sub) |>.lower
--   let g_lower := g.rest sub |>.lower' e_sub
--   let g'_lower ← g'.lower
--   g_lower.replace e_sub g'_lower |>.higher

@[drunfold]
def rename [FreshIdent Ident]
    (typ : Ident) (p : PortMapping Ident) (g : ExprHigh Ident) : Option (ExprHigh Ident) := do
  let g_lower ← g.lower
  g_lower.rename typ p |>.higher

def renamePorts (g : ExprHigh String) (p : PortMapping String) := do
  let g_lower ← g.lower
  g_lower.renamePorts p >>= ExprLow.higherSS

end ExprHigh

def updatePortMappingInput {α} [Inhabited α] (s : Std.HashMap String (PortMapping String × α))
  (inCluster : Bool)
  (inPort : InternalPort String)
  : Bool → InternalPort String → Std.HashMap String (PortMapping String × α)
| _, co@⟨.top, n⟩ =>
  match (inCluster, inPort) with
  | (true, ci@⟨.internal x, y⟩) =>
    let (a, b) := s[x]!
    s.insert x ({a with output := a.output.cons ci co}, b)
  | (false, ⟨.internal x, y⟩) =>
    let (a, b) := s[x]!
    s.insert x ({a with output := a.output.cons ⟨.top, y⟩ co}, b)
  | _ => s
| false, c@⟨.internal i, x⟩ =>
  let (a, b) := s[i]!
  s.insert i ({a with input := a.input.cons ⟨.top, x⟩ c}, b)
| true, ⟨.internal _, _⟩ => s

def updatePortMappingOutput {α} [Inhabited α] (s : Std.HashMap String (PortMapping String × α))
  (inCluster : Bool)
  (inPort : InternalPort String)
  : Bool → InternalPort String → Std.HashMap String (PortMapping String × α)
| _, co@⟨.top, n⟩ =>
  match (inCluster, inPort) with
  | (true, ci@⟨.internal x, y⟩) =>
    let (a, b) := s[x]!
    s.insert x ({a with input := a.input.cons ci co}, b)
  | (false, ⟨.internal x, y⟩) =>
    let (a, b) := s[x]!
    s.insert x ({a with input := a.input.cons ⟨.top, y⟩ co}, b)
  | _ => s
| false, c@⟨.internal i, x⟩ =>
  let (a, b) := s[i]!
  s.insert i ({a with output := a.output.cons ⟨.top, x⟩ c}, b)
| true, ⟨.internal _, _⟩ => s

def parseInternalPort (s : String) : Option (InternalPort String) :=
  match s.splitOn "." with
  | [single] => some ⟨.top, single⟩
  | [first, second] => some ⟨.internal first, second⟩
  | _ => none

structure InstMaps where
  instMap : Std.HashMap String (InstIdent String × Bool)
  instTypeMap : Std.HashMap String (PortMapping String × String)

def updateNodeMaps (maps : InstMaps) (inst typ : String) (cluster : Bool := false) : Except String InstMaps := do
  let mut instMap := maps.instMap
  let mut instTypeMap := maps.instTypeMap
  let mut modInst : InstIdent String := .top
  unless typ == "io" do modInst := .internal inst
  let (b, map') := instMap.containsThenInsertIfNew inst (modInst, cluster)
  if !b then
    instMap := map'
    -- IO "modules" are not added to the instTypeMap.
    unless typ == "io" do instTypeMap := instTypeMap.insert inst (∅, typ)
  else
    throw s!"Multiple references to {inst} found"
  return ⟨instMap, instTypeMap⟩

inductive ConnError where
| outInstError (s : String)
| inInstError (s : String)
| portError (s : String)

def ConnError.toString : ConnError → String
| .outInstError s => s
| .inInstError s => s
| .portError s => s

instance : ToString ConnError where
  toString c := c.toString

def updateConnMaps (maps : InstMaps) (conns : List (Connection String))
    (outInst inInst : String) (outP inP : Option String)
    : Except ConnError (InstMaps × List (Connection String)) := do
  let mut out := outP
  let mut inp := inP
  let some aInst := maps.instMap[outInst]? | throw (.outInstError s!"Instance has not been declared: {outInst}")
  let some bInst := maps.instMap[inInst]? | throw (.inInstError s!"Instance has not been declared: {inInst}")
  if aInst.fst = .top && bInst.fst = .top then
    throw <| .outInstError s!"Both the output \"{outInst}\" and input \"{inInst}\" are IO ports"
  -- If no port name is provided and the port is a top-level port, then use
  -- the instance name as the port name.
  if out.isNone && aInst.fst.isTop then out := some outInst
  if inp.isNone && bInst.fst.isTop then inp := some inInst
  let some out' := out | throw <| .portError s!"No output found for: {aInst}"
  let some inp' := inp | throw <| .portError s!"No input found for: {bInst}"
  let some outPort := parseInternalPort out'
    | throw <| .portError s!"Output port format incorrect: {out'}"
  let some inPort := parseInternalPort inp'
    | throw <| .portError s!"Input port format incorrect: {inp'}"
  -- If the instance is a cluster do not modify the name, otherwise as the
  -- instance as a prefix.
  let outPort' := if aInst.snd then outPort else ⟨aInst.fst, outPort.name⟩
  let inPort' := if bInst.snd then inPort else ⟨bInst.fst, inPort.name⟩
  -- If one of the end points is an external port then do not add a
  -- connection into the graph.
  let mut conns := conns
  let mut instTypeMap := maps.instTypeMap
  unless aInst.fst = .top || bInst.fst = .top do
    conns := ⟨ outPort', inPort' ⟩ :: conns
    instTypeMap := updatePortMappingOutput instTypeMap bInst.snd inPort' aInst.snd outPort'
    instTypeMap := updatePortMappingInput instTypeMap aInst.snd outPort' bInst.snd inPort'
  if aInst.fst = .top then
    instTypeMap := updatePortMappingOutput instTypeMap bInst.snd inPort' aInst.snd outPort'
  if bInst.fst = .top then
    instTypeMap := updatePortMappingInput instTypeMap aInst.snd outPort' bInst.snd inPort'
  return (⟨maps.instMap, instTypeMap⟩, conns)

end DataflowRewriter
