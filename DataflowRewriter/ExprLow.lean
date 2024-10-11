/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.Module
import DataflowRewriter.Simp

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
  | base : Ident → Ident → ExprLow Ident
  | input : InternalPort Ident → Ident → ExprLow Ident → ExprLow Ident
  | output : InternalPort Ident → Ident → ExprLow Ident → ExprLow Ident
  | product : ExprLow Ident → ExprLow Ident → ExprLow Ident
  | connect : InternalPort Ident → InternalPort Ident → ExprLow Ident → ExprLow Ident
  deriving Repr, Hashable, Ord, Inhabited, DecidableEq

namespace ExprLow

variable {Ident}
variable [DecidableEq Ident]

@[drunfold] def build_module' (ε : IdentMap Ident ((T: Type _) × Module Ident T))
    : ExprLow Ident → Option ((T: Type _) × Module Ident T)
  | .base i e => do
    let mod ← ε.find? e
    return ⟨ mod.1, mod.2.renamePorts (λ ⟨ _, y ⟩ => ⟨ .internal i, y ⟩ ) ⟩
  | .input a b e' => do
    let e ← build_module' ε e'
    return ⟨ e.1, e.2.renameToInput (λ p => if p == a then ⟨ .top, b ⟩ else p) ⟩
  | .output a b e' => do
    let e ← build_module' ε e'
    return ⟨ e.1, e.2.renameToOutput (λ p => if p == a then ⟨ .top, b ⟩ else p) ⟩
  | .connect o i e' => do
    let e ← build_module' ε e'
    return ⟨e.1, e.2.connect' o i⟩
  | .product a b => do
    let a <- build_module' ε a;
    let b <- build_module' ε b;
    return ⟨a.1 × b.1, a.2.product b.2⟩

@[drunfold] def build_module (ε : IdentMap Ident (Σ (T : Type _), Module Ident T))
    (e : ExprLow Ident)
    (h : (build_module' ε e).isSome = true := by rfl)
    : (T : Type _) × Module Ident T := build_module' ε e |>.get h

theorem build_module_modify {ε : IdentMap Ident (Σ (T : Type), Module Ident T)} {expr} {m : (Σ (T : Type), Module Ident T)} {i : Ident} :
  (build_module' ε expr).isSome → (build_module' (ε.modify i (λ _ _ => m)) expr).isSome := by sorry

section Refinement

universe v w

variable {Ident : Type w}
variable [DecidableEq Ident]
variable [Inhabited Ident]

variable (ε : IdentMap Ident ((T : Type) × Module Ident T))
variable (iexpr : ExprLow Ident)
variable (hiexpr : (build_module' ε iexpr).isSome)

variable {S : Type v}
variable (smod : Module Ident S)

variable [MatchInterface (build_module ε iexpr hiexpr).2 smod]

def refines_φ (R : (build_module ε iexpr hiexpr).1 → S → Prop) :=
  (build_module ε iexpr hiexpr).2 ⊑_{R} smod

def refines := ∃ R, (build_module ε iexpr hiexpr).2 ⊑_{R} smod

notation:35 x " ⊑ₑ_{" f:35 "} " y:34 => refines_φ x y f
notation:35 x " ⊑ₑ " y:34 => refines x y

theorem substitution {T ident mod} {mod' : Module Ident T}
        [MatchInterface (build_module (ε.modify ident (λ _ _ => ⟨T, mod'⟩)) iexpr (build_module_modify hiexpr)).2 smod]
        [MatchInterface mod mod']
        (R : (build_module ε iexpr hiexpr).1 → S → Prop) :
  (build_module ε iexpr hiexpr).2 ⊑ smod →
  ε.find? ident = some ⟨ T, mod ⟩ →
  mod ⊑ mod' →
  (build_module (ε.modify ident (λ _ _ => ⟨T, mod'⟩)) iexpr (build_module_modify hiexpr)).2 ⊑ smod := by sorry

end Refinement

end ExprLow
end DataflowRewriter
