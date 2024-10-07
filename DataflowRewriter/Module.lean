/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Lean
import Leanses
import Qq

import DataflowRewriter.Simp
import DataflowRewriter.List
import DataflowRewriter.AssocList

open Batteries (AssocList)

deriving instance Repr for AssocList

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

/--
If only an identifier is provided, it can be coerced into an `InternalPort
Ident` by using `InstIdent.top` as the instance name, creating a port for the
top-level module.
-/
instance {Ident} [Inhabited Ident] : Coe Ident (InternalPort Ident) where
  coe a := ⟨InstIdent.top, a⟩

abbrev IdentMap Ident α := AssocList Ident α
abbrev IdentSet Ident := Finset Ident

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
variable [Inhabited Ident]

/--
Get an IO port using external IO ports, i.e. `InternalPort Ident` with the
instance set to `top`.
-/
def getIO.{u₁, u₂} {S : Type u₁} 
    (l: PortMap Ident (Σ T : Type u₂, (S → T → S → Prop))) (n : Ident)
    : Σ T : Type u₂, (S → T → S → Prop) := 
  l.find? ↑n |>.getD (⟨ PUnit, λ _ _ _ => True ⟩)

/--
Get any internal port from the `PortMap`.
-/
def getInternalPort.{u₁, u₂} {S : Type u₁} 
    (l: PortMap Ident (Σ T : Type u₂, (S → T → S → Prop))) 
    (n : InternalPort Ident)
    : Σ T : Type u₂, (S → T → S → Prop) :=
  l.find? n |>.getD (⟨ PUnit, λ _ _ _ => True ⟩)

end PortMap

/--
`Module'` definition, which is our definition of circuit semantics.  It can have
inputs and outputs, which are maps from `Ident` to transition rules accept or
return a value.
-/
structure Module' (Ident S : Type _) where
  inputs : PortMap Ident (Σ T : Type, (S → T → S → Prop))
  outputs : PortMap Ident (Σ T : Type, (S → T → S → Prop))
  internals : List (S → S → Prop)
  deriving Inhabited

-- mklenses Module
-- open Module.l

namespace Module'

/--
The empty module, which should also be the `default` module.
-/
def empty {Ident S : Type _} : Module' Ident S := {inputs := ∅, outputs := ∅, internals:= ∅}

theorem empty_is_default {Ident S} : @empty Ident S = default := Eq.refl _

variable {Ident : Type _}
variable [DecidableEq Ident]
variable [Inhabited Ident]

def liftL {S S'} (x: (T : Type _) × (S → T → S → Prop)) 
    : (T : Type _) × (S × S' → T → S × S' → Prop) :=
  ⟨ x.1, λ (a,b) ret (a',b') => x.2 a ret a' ∧ b = b' ⟩

def liftR {S S'} (x: (T : Type _) × (S' → T → S' → Prop)) 
    : (T : Type _) × (S × S' → T → S × S' → Prop) :=
  ⟨ x.1, λ (a,b) ret (a',b') => x.2 b ret b' ∧ a = a' ⟩

def liftL' {S S'} (x:  S → S → Prop) : S × S' → S × S' → Prop :=
  λ (a,b) (a',b') => x a a' ∧ b = b'

def liftR' {S S'} (x:  S' → S' → Prop) : S × S' → S × S' → Prop :=
  λ (a,b) (a',b') => x b b' ∧ a = a'

/--
`connect'` will produce a new rule that fuses an input with an output, with a
precondition that the input and output type must match.
-/
def connect' {S : Type _} (mod : Module' Ident S) (o i : InternalPort Ident) : Module' Ident S :=
  { inputs := mod.inputs.erase i ,
    outputs :=  mod.outputs.erase o,
    internals := 
      (λ st st' => 
        ∀ wf : (mod.inputs.getInternalPort i).1 = (mod.outputs.getInternalPort o).1,
          ∃ consumed_output output, (mod.outputs.getInternalPort o).2 st output consumed_output 
            ∧ (mod.inputs.getInternalPort i).2 consumed_output (wf.mpr output) st')
      :: mod.internals }

def product {S S'} (mod1 : Module' Ident S) (mod2: Module' Ident S') : Module' Ident (S × S') :=
  { inputs := (mod1.inputs.mapVal (λ _ => liftL)).append (mod2.inputs.mapVal (λ _ => liftR)),
    outputs := (mod1.outputs.mapVal (λ _ => liftL)).append (mod2.outputs.mapVal (λ _ => liftR)),
    internals := mod1.internals.map liftL' ++ mod2.internals.map liftR'
  }

def renamePorts {S} (mod : Module' Ident S) (f : InternalPort Ident → InternalPort Ident) : Module' Ident S :=
  { inputs := mod.inputs.modifyKeys f,
    outputs := mod.outputs.modifyKeys f,
    internals := mod.internals
  }

def renameToInput {S} (mod : Module' Ident S) (f : InternalPort Ident → InternalPort Ident) : Module' Ident S :=
  { inputs := mod.inputs.modifyKeys f,
    outputs := mod.outputs,
    internals := mod.internals
  }

def renameToOutput {S} (mod : Module' Ident S) (f : InternalPort Ident → InternalPort Ident) : Module' Ident S :=
  { inputs := mod.inputs,
    outputs := mod.outputs.modifyKeys f,
    internals := mod.internals
  }

end Module'

/-
The following definition lives in `Type`, I'm not sure if a type class can live
in `Prop` even though it seems to be accepted.
-/

variable {Ident} [DecidableEq Ident] [Inhabited Ident] in

/--
Match two interfaces of two modules, which implies that the types of all the
input and output rules match.
-/
class MatchInterface {I S} (imod : Module' Ident I) (smod : Module' Ident S) where
  input_types : ∀ (ident : Ident), (imod.inputs.getIO ident).1 = (smod.inputs.getIO ident).1
  output_types : ∀ (ident : Ident), (imod.outputs.getIO ident).1 = (smod.outputs.getIO ident).1

/--
State that there exists zero or more internal rule executions to reach a final
state from an initial state.
-/
inductive existSR {Ident S : Type _} (mod : Module' Ident S) : S → S → Prop where
  | done : ∀ init, existSR mod init init
  | step : ∀ init mid final rule,
      rule ∈ mod.internals →
      rule init mid →
      existSR mod mid final →
      existSR mod init final

section Refinement

variable {I : Type _}
variable {S : Type _}
variable {Ident : Type _}
variable [DecidableEq Ident]
variable [Inhabited Ident]

variable (imod : Module' Ident I)
variable (smod : Module' Ident S)

variable [mm : MatchInterface imod smod]

/-
This could be made even more flexible by passing a custom type comparison
function for the inputs and outputs.  For now this might be general enough
though.
-/
structure indistinguishable (init_i : I) (init_s : S) : Prop where
  inputs_indistinguishable : ∀ (ident : Ident) new_i v,
    imod.inputs.contains ↑ident →
    (imod.inputs.getIO ident).2 init_i v new_i →
    ∃ new_s, (smod.inputs.getIO ident).2 init_s ((mm.input_types ident).mp v) new_s
  outputs_indistinguishable : ∀ ident new_i v,
    imod.outputs.contains ↑ident →
    (imod.outputs.getIO ident).2 init_i v new_i →
    ∃ new_s, (smod.outputs.getIO ident).2 init_s ((mm.output_types ident).mp v) new_s

structure comp_refines (R : I → S → Prop) (init_i : I) (init_s : S) : Prop where
  inputs :
    ∀ ident mid_i v,
      imod.inputs.contains ↑ident →
      (imod.inputs.getIO ident).2 init_i v mid_i →
      ∃ almost_mid_s mid_s,
        (smod.inputs.getIO ident).2 init_s ((mm.input_types ident).mp v) almost_mid_s
        ∧ existSR smod almost_mid_s mid_s
        ∧ R mid_i mid_s
        ∧ indistinguishable imod smod mid_i mid_s
  outputs :
    ∀ ident mid_i v,
      imod.outputs.contains ↑ident →
      (imod.outputs.getIO ident).2 init_i v mid_i →
      ∃ almost_mid_s mid_s,
        (smod.outputs.getIO ident).2 init_s ((mm.output_types ident).mp v) almost_mid_s
        ∧ existSR smod almost_mid_s mid_s
        ∧ R mid_i mid_s
        ∧ indistinguishable imod smod mid_i mid_s
  internals :
    ∀ rule mid_i,
      rule ∈ imod.internals →
      rule init_i mid_i →
      ∃ mid_s,
        existSR smod init_s mid_s
        ∧ R mid_i mid_s
        ∧ indistinguishable imod smod mid_i mid_s

def refines (R : I → S → Prop) :=
  ∀ (init_i : I) (init_s : S),
    R init_i init_s →
    indistinguishable imod smod init_i init_s →
    comp_refines imod smod R init_i init_s

end Refinement

instance {n} : OfNat (InternalPort Nat) n where
  ofNat := ⟨ .top, n ⟩

abbrev Module := Module' Nat

abbrev StringModule := Module' String

end DataflowRewriter
