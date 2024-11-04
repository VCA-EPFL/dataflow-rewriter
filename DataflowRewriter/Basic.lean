/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Lean
import Batteries

import DataflowRewriter.AssocList.Basic
import DataflowRewriter.Simp

open Batteries (AssocList)

namespace DataflowRewriter

/--
An instance may refer to an internal instance by name, or it may refer to the
current (top-level) module.
-/
inductive InstIdent (Ident : Type _) where
| top : InstIdent Ident
| internal : Ident → InstIdent Ident
deriving Inhabited, Ord, Hashable, Repr, DecidableEq

instance {Ident} [ToString Ident] : ToString (InstIdent Ident) where
  toString
  | .top => "io"
  | .internal i => toString i

namespace InstIdent

def elem {Ident} [BEq Ident] (instances : List Ident) : InstIdent Ident → Bool
| .top => false
| .internal i => instances.contains i

def isTop {Ident} : InstIdent Ident → Bool
| .top => true
| _ => false

def isInternal {Ident} : InstIdent Ident → Bool
| .internal .. => true
| _ => false

end InstIdent

/--
Internal port parametrised by the `Ident` identifier type.  A port consist of an
instance `inst` it belongs to and a port `name` of that instance.
-/
structure InternalPort (Ident : Type _) where
  inst : InstIdent Ident
  name : Ident
deriving Repr, Hashable, Ord, Inhabited, DecidableEq

def InternalPort.map {α β} (f : α → β) : InternalPort α → InternalPort β
| ⟨ .top, a ⟩ => ⟨ .top, f a ⟩
| ⟨ .internal b, a ⟩ => ⟨ .internal (f b), f a ⟩

instance {Ident} [ToString Ident] : ToString (InternalPort Ident) where
  toString | ⟨.internal a, b⟩ => toString a ++ " " ++ toString b
           | ⟨.top, b⟩ => toString b

/--
If only an identifier is provided, it can be coerced into an `InternalPort
Ident` by using `InstIdent.top` as the instance name, creating a port for the
top-level module.
-/
instance {Ident} [Inhabited Ident] : Coe Ident (InternalPort Ident) where
  coe a := ⟨InstIdent.top, a⟩

abbrev IdentMap Ident α := AssocList Ident α

namespace IdentMap

def replace_env {Ident α} [DecidableEq Ident] (ε : IdentMap Ident α) {ident mod}
  (h : ε.mem ident mod) mod' :=
  (ε.replace ident mod')

notation:25 "{" ε " | " h " := " mod' "}" => replace_env ε h mod'

end IdentMap

/--
Mapping from `Ident` to any type `α`.  This was chosen to be an AssocList
because it seems like it is the simplest data-structure for performing
reduction.  `RBMap` currently does not work for `whnf` reduction due to
exponential reduction behaviour in `Meta.whnf`.
-/
abbrev PortMap Ident α := AssocList (InternalPort Ident) α

namespace PortMap

variable {Ident}
variable [DecidableEq Ident]

/--
Get an IO port using external IO ports, i.e. `InternalPort Ident` with the
instance set to `top`.
-/
@[drunfold] def getIO.{u₁, u₂} {S : Type u₁}
    (l : PortMap Ident (Σ T : Type u₂, (S → T → S → Prop)))
    (n : InternalPort Ident)
    : Σ T : Type u₂, (S → T → S → Prop) :=
  l.find? n |>.getD (⟨ PUnit, λ _ _ _ => True ⟩)

theorem getIO_none {S} (m : PortMap Ident ((T : Type) × (S → T → S → Prop)))
        (ident : InternalPort Ident) :
  m.find? ident = none ->
  m.getIO ident = ⟨ PUnit, λ _ _ _ => True ⟩ := by
  intros H; simp only [PortMap.getIO, H]; simp

theorem getIO_some {S} (m : PortMap Ident ((T : Type) × (S → T → S → Prop)))
        (ident : InternalPort Ident) t :
  m.find? ident = some t ->
  m.getIO ident = t := by
  intros H; simp only [PortMap.getIO, H]; simp

end PortMap

structure PortMapping (Ident) where
  input : PortMap Ident (InternalPort Ident)
  output : PortMap Ident (InternalPort Ident)
deriving Repr, Inhabited, DecidableEq

instance (Ident) [Repr Ident] : ToString (InternalPort Ident) where
  toString i := repr i |>.pretty

instance (Ident) [Repr Ident] : ToString (PortMapping Ident) where
  toString i := repr i |>.pretty

namespace PortMapping

variable {Ident}

def append (a b : PortMapping Ident) :=
  PortMapping.mk (a.input ++ b.input) (a.output ++ b.output)

instance : Append (PortMapping Ident) := ⟨append⟩

instance : EmptyCollection (PortMapping Ident) := ⟨⟨∅, ∅⟩⟩

def ofPortMapping [DecidableEq Ident] (p : PortMapping Ident) : Option Ident :=
  match p.input with
  | .cons ⟨.top, _⟩ ⟨.internal i, _⟩ _ =>
    if p.input.all (λ | ⟨.top, a⟩, ⟨.internal i', b⟩ => a = b && i = i'
                      | _, _ => false)
       && p.output.all (λ | ⟨.top, a⟩, ⟨.internal i', b⟩ => a = b && i = i'
                          | _, _ => false)
    then some i
    else none
  | _ => none

def map {α β} (f : α → β) : PortMapping α → PortMapping β
| ⟨ a, b ⟩ => ⟨a.mapKey (λ k => k.map f) |>.mapVal (λ _ v => v.map f)
              , b.mapKey (λ k => k.map f ) |>.mapVal (λ _ v => v.map f)⟩

def inverse (p : PortMapping Ident) :=
  {p with input := p.input.inverse, output := p.output.inverse}

end PortMapping

structure Interface (Ident) where
  input : List (InternalPort Ident)
  output : List (InternalPort Ident)

namespace Interface

variable {Ident}

def allInst (f : InstIdent Ident → Bool) (i : Interface Ident) : Bool :=
  i.input.all (·.inst |> f) && i.output.all (·.inst |> f)

def isBaseModule (i : Interface Ident) : Bool := i.allInst (·.isTop)

def toIdentityPortMapping (i : Interface Ident) : PortMapping Ident :=
  ⟨(i.input.map (λ a => (a, a))).toAssocList,
   (i.output.map (λ a => (a, a))).toAssocList⟩

def toPortMapping (i : Interface Ident) (ident : Ident) : PortMapping Ident :=
  if i.isBaseModule
  then ⟨(i.input.map (λ a => (a, InternalPort.mk (.internal ident) a.name))).toAssocList,
        (i.output.map (λ a => (a, InternalPort.mk (.internal ident) a.name))).toAssocList⟩
  else i.toIdentityPortMapping

end Interface

def PortMapping.toInterface {Ident} (p : PortMapping Ident) : Interface Ident :=
  ⟨p.input.keysList, p.output.keysList⟩

end DataflowRewriter
