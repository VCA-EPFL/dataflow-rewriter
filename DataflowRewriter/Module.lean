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
import DataflowRewriter.HVector

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
@[drunfold] def getIO.{u₁, u₂} {S : Type u₁}
    (l: PortMap Ident (Σ T : Type u₂, (S → T → S → Prop))) (n : Ident)
    : Σ T : Type u₂, (S → T → S → Prop) :=
  l.find? ↑n |>.getD (⟨ PUnit, λ _ _ _ => True ⟩)

theorem getIO_none {S} (m : PortMap Ident ((T : Type) × (S → T → S → Prop)))
        (ident : Ident) :
  m.find? ↑ident = none ->
  m.getIO ident = ⟨ PUnit, λ _ _ _ => True ⟩ := by
  intros H; simp only [PortMap.getIO, H]; simp

theorem getIO_some {S} (m : PortMap Ident ((T : Type) × (S → T → S → Prop)))
        (ident : Ident) t :
  m.find? ↑ident = some t ->
  m.getIO ident = t := by
  intros H; simp only [PortMap.getIO, H]; simp

/--
Get any internal port from the `PortMap`.
-/
@[drunfold] def getInternalPort.{u₁, u₂} {S : Type u₁}
    (l: PortMap Ident (Σ T : Type u₂, (S → T → S → Prop)))
    (n : InternalPort Ident)
    : Σ T : Type u₂, (S → T → S → Prop) :=
  l.find? n |>.getD (⟨ PUnit, λ _ _ _ => True ⟩)

end PortMap

/--
`Module` definition, which is our definition of circuit semantics.  It can have
inputs and outputs, which are maps from `Ident` to transition rules accept or
return a value.
-/
structure Module (Ident S : Type _) where
  inputs : PortMap Ident (Σ T : Type, (S → T → S → Prop))
  outputs : PortMap Ident (Σ T : Type, (S → T → S → Prop))
  internals : List (S → S → Prop)
  deriving Inhabited

-- mklenses Module
-- open Module.l

namespace Module

/--
The empty module, which should also be the `default` module.
-/
@[drunfold] def empty {Ident : Type _} S : Module Ident S := {inputs := ∅, outputs := ∅, internals:= ∅}

theorem empty_is_default {Ident S} : @empty Ident S = default := Eq.refl _

universe i

variable {Ident : Type i}
variable [DecidableEq Ident]
variable [Inhabited Ident]

@[drunfold] def liftL {S S' : Type _} (x: (T : Type _) × (S → T → S → Prop))
    : (T : Type _) × (S × S' → T → S × S' → Prop) :=
  ⟨ x.1, λ (a,b) ret (a',b') => x.2 a ret a' ∧ b = b' ⟩

@[drunfold] def liftR {S S'} (x: (T : Type _) × (S' → T → S' → Prop))
    : (T : Type _) × (S × S' → T → S × S' → Prop) :=
  ⟨ x.1, λ (a,b) ret (a',b') => x.2 b ret b' ∧ a = a' ⟩

@[drunfold] def liftL' {S S'} (x:  S → S → Prop) : S × S' → S × S' → Prop :=
  λ (a,b) (a',b') => x a a' ∧ b = b'

@[drunfold] def liftR' {S S'} (x:  S' → S' → Prop) : S × S' → S × S' → Prop :=
  λ (a,b) (a',b') => x b b' ∧ a = a'

@[drunfold] def liftLD {α : Type _} {l₁ l₂ : List α} {f} (x: (T : Type _) × (HVector f l₁ → T → HVector f l₁ → Prop))
    : (T : Type _) × (HVector f (l₁ ++ l₂) → T → HVector f (l₁ ++ l₂) → Prop) :=
  ⟨ x.1, λ a ret a' => x.2 a.left ret a'.left ∧ a.right = a'.right ⟩

@[drunfold] def liftRD {α : Type _} {l₁ l₂ : List α} {f} (x: (T : Type _) × (HVector f l₂ → T → HVector f l₂ → Prop))
    : (T : Type _) × (HVector f (l₁ ++ l₂) → T → HVector f (l₁ ++ l₂) → Prop) :=
  ⟨ x.1, λ a ret a' => x.2 a.right ret a'.right ∧ a.left = a'.left ⟩

@[drunfold] def liftLD' {α : Type _} {l₁ l₂ : List α} {f} (x: HVector f l₁ → HVector f l₁ → Prop)
    : HVector f (l₁ ++ l₂) → HVector f (l₁ ++ l₂) → Prop :=
  λ a a' => x a.left a'.left ∧ a.right = a'.right

@[drunfold] def liftRD' {α : Type _} {l₁ l₂ : List α} {f} (x: HVector f l₂ → HVector f l₂ → Prop)
    : HVector f (l₁ ++ l₂) → HVector f (l₁ ++ l₂) → Prop :=
  λ a a' => x a.right a'.right ∧ a.left = a'.left

@[drunfold] def liftSingle.{u} {α} {a : α} {f} (x: Σ (T : Type u), (f a → T → f a → Prop))
    : Σ (T : Type u), HVector f [a] → T → HVector f [a] → Prop :=
  ⟨ x.1, λ | .cons a .nil, t, .cons a' .nil => x.2 a t a' ⟩

@[drunfold] def liftSingle' {α} {a : α} {f} (x: f a → f a → Prop)
    : HVector f [a] → HVector f [a] → Prop :=
  λ | .cons a .nil, .cons a' .nil => x a a'

/--
`connect'` will produce a new rule that fuses an input with an output, with a
precondition that the input and output type must match.
-/
@[drunfold] def connect' {S : Type _} (mod : Module Ident S) (o i : InternalPort Ident) : Module Ident S :=
  { inputs := mod.inputs.erase i ,
    outputs :=  mod.outputs.erase o,
    internals :=
      (λ st st' =>
        ∀ wf : (mod.inputs.getInternalPort i).1 = (mod.outputs.getInternalPort o).1,
          ∃ consumed_output output, (mod.outputs.getInternalPort o).2 st output consumed_output
            ∧ (mod.inputs.getInternalPort i).2 consumed_output (wf.mpr output) st')
      :: mod.internals }

@[drunfold] def product {S S'} (mod1 : Module Ident S) (mod2: Module Ident S') : Module Ident (S × S') :=
  { inputs := (mod1.inputs.mapVal (λ _ => liftL)).append (mod2.inputs.mapVal (λ _ => liftR)),
    outputs := (mod1.outputs.mapVal (λ _ => liftL)).append (mod2.outputs.mapVal (λ _ => liftR)),
    internals := mod1.internals.map liftL' ++ mod2.internals.map liftR'
  }

@[drunfold] def productD {α} {l₁ l₂ : List α} {f} (mod1 : Module Ident (HVector f l₁)) (mod2: Module Ident (HVector f l₂)) : Module Ident (HVector f (l₁ ++ l₂)) :=
  { inputs := (mod1.inputs.mapVal (λ _ => liftLD)).append (mod2.inputs.mapVal (λ _ => liftRD)),
    outputs := (mod1.outputs.mapVal (λ _ => liftLD)).append (mod2.outputs.mapVal (λ _ => liftRD)),
    internals := mod1.internals.map liftLD' ++ mod2.internals.map liftRD'
  }

@[drunfold] def liftD {α} {e : α} {f} (mod : Module Ident (f e)) : Module Ident (HVector f [e]) :=
  { inputs := mod.inputs.mapVal λ _ => liftSingle,
    outputs := mod.outputs.mapVal λ _ => liftSingle,
    internals := mod.internals.map liftSingle'
  }

@[drunfold] def renamePorts {S : Type _} (mod : Module Ident S) (f : InternalPort Ident → InternalPort Ident) : Module Ident S :=
  { inputs := mod.inputs.modifyKeys f,
    outputs := mod.outputs.modifyKeys f,
    internals := mod.internals
  }

@[drunfold] def renameToInput {S} (mod : Module Ident S) (f : InternalPort Ident → InternalPort Ident) : Module Ident S :=
  { inputs := mod.inputs.modifyKeys f,
    outputs := mod.outputs,
    internals := mod.internals
  }

@[drunfold] def renameToOutput {S} (mod : Module Ident S) (f : InternalPort Ident → InternalPort Ident) : Module Ident S :=
  { inputs := mod.inputs,
    outputs := mod.outputs.modifyKeys f,
    internals := mod.internals
  }

end Module

section Match

/-
The following definition lives in `Type`, I'm not sure if a type class can live
in `Prop` even though it seems to be accepted.
-/

variable {Ident}
variable [DecidableEq Ident]
variable {I S}

/--
Match two interfaces of two modules, which implies that the types of all the
input and output rules match.
-/
class MatchInterface (imod : Module Ident I) (smod : Module Ident S) : Prop where
  input_types : ∀ (ident : Ident), (imod.inputs.getIO ident).1 = (smod.inputs.getIO ident).1
  output_types : ∀ (ident : Ident), (imod.outputs.getIO ident).1 = (smod.outputs.getIO ident).1

theorem match_interface_empty {smod : Module Ident S} [MatchInterface (@Module.empty Ident I) smod]
  : ∀ I', MatchInterface (@Module.empty Ident I') smod := sorry

end Match


/--
State that there exists zero or more internal rule executions to reach a final
state from an initial state.
-/
inductive existSR {Ident S : Type _} (mod : Module Ident S) : S → S → Prop where
  | done : ∀ init, existSR mod init init
  | step : ∀ init mid final rule,
      rule ∈ mod.internals →
      rule init mid →
      existSR mod mid final →
      existSR mod init final

namespace Module

section Refinement

variable {I : Type _}
variable {S : Type _}
variable {Ident : Type _}
variable [DecidableEq Ident]
variable [Inhabited Ident]

variable (imod : Module Ident I)
variable (smod : Module Ident S)

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
  outputs :
    ∀ ident mid_i v,
      imod.outputs.contains ↑ident →
      (imod.outputs.getIO ident).2 init_i v mid_i →
      ∃ almost_mid_s mid_s,
        (smod.outputs.getIO ident).2 init_s ((mm.output_types ident).mp v) almost_mid_s
        ∧ existSR smod almost_mid_s mid_s
        ∧ R mid_i mid_s
  internals :
    ∀ rule mid_i,
      rule ∈ imod.internals →
      rule init_i mid_i →
      ∃ mid_s,
        existSR smod init_s mid_s
        ∧ R mid_i mid_s

def refines_φ (R : I → S → Prop) :=
  ∀ (init_i : I) (init_s : S),
    R init_i init_s →
    comp_refines imod smod R init_i init_s

notation:35 x " ⊑_{" R:35 "} " y:34 => refines_φ x y R

omit mm in
def refines :=
  ∃ (mm : MatchInterface imod smod) (R : I → S → Prop),
    imod ⊑_{fun x y => indistinguishable imod smod x y ∧ R x y} smod

notation:35 x " ⊑ " y:34 => refines x y

omit [Inhabited Ident] in
theorem refines_φ_refines {φ} :
  (∀ i_init s_init, φ i_init s_init → indistinguishable imod smod i_init s_init) →
  imod ⊑_{φ} smod →
  imod ⊑ smod := by
  intro Hind Href
  -- exists φ
  -- intro init_i init_s ⟨ Hphi, Hindis ⟩
  -- specialize Href init_i init_s Hindis
  -- rcases Href with ⟨ Hin, Hout, Hint ⟩; constructor
  -- · intro ident mid_i v Hcont Hrule
  --   specialize Hin ident mid_i v Hcont Hrule
  --   tauto
  -- · intro ident mid_i v Hcont Hrule
  --   specialize Hout ident mid_i v Hcont Hrule
  --   tauto
  -- · intro rule mid_i Hcont Hrule
  --   specialize Hint rule mid_i Hcont Hrule
  --   tauto
  sorry

end Refinement

theorem empty_refines {Ident S I₁ I₂} [DecidableEq Ident] {smod : Module Ident S} :
  empty I₁ ⊑ smod →
  empty I₂ ⊑ smod := by sorry

end Module

instance {n} : OfNat (InstIdent Nat) n where
  ofNat := .internal n

instance {n} : OfNat (InternalPort Nat) n where
  ofNat := ⟨ .top, n ⟩

abbrev NatModule := Module Nat

abbrev StringModule := Module String

end DataflowRewriter
