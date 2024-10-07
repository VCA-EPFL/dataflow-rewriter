/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.Module

namespace DataflowRewriter

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

def build_module' (e : ExprLow Ident) (ε : IdentMap Ident ((T: Type _) × Module' Ident T))
    : Option ((T: Type _) × Module' Ident T) := do
  match e with
  | .base i e =>
    let mod ← ε.find? e
    return ⟨ mod.1, mod.2.renamePorts (λ ⟨ _, y ⟩ => ⟨ .internal i, y ⟩ ) ⟩
  | .input a b e' =>
    let e ← build_module' e' ε
    return ⟨ e.1, e.2.renameToInput (λ p => if p == a then ⟨ .top, b ⟩ else p) ⟩
  | .output a b e' =>
    let e ← build_module' e' ε
    return ⟨ e.1, e.2.renameToOutput (λ p => if p == a then ⟨ .top, b ⟩ else p) ⟩
  | .connect o i e' =>
    let e ← build_module' e' ε
    return ⟨e.1, e.2.connect' o i⟩
  | .product a b =>
    let a <- build_module' a ε;
    let b <- build_module' b ε;
    return ⟨a.1 × b.1, a.2.product b.2⟩

def build_module (e : ExprLow Ident) (ε : IdentMap Ident ((T : Type _) × Module' Ident T)) 
    (h : (build_module' e ε).isSome = true := by decide)
    : (T : Type _) × Module' Ident T := build_module' e ε |>.get h

end ExprLow

end DataflowRewriter
