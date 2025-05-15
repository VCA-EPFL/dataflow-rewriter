import DataflowRewriter.Module
import DataflowRewriter.Component
import DataflowRewriter.ModuleReduction
import DataflowRewriter.ExprLow
import DataflowRewriter.ExprLowLemmas

open Batteries (AssocList)

namespace DataflowRewriter.Examples

def ε : Env :=
  [("Empty", ⟨_, StringModule.empty⟩)].toAssocList

@[drenv] def empty_in_ε :
  AssocList.find? "Empty" ε = .some ⟨_, StringModule.empty⟩ := by rfl

@[drunfold_defs]
def nproduct {α} (n : Nat) (base : ExprLow α) (f : Nat → ExprLow α) : ExprLow α :=
  List.foldl (λ acc i => ExprLow.product acc (f i)) base (List.range n)

@[drunfold_defs]
def empty : ExprLow String :=
  ExprLow.base { input := .nil, output := .nil } "Empty"

@[drunfold_defs]
def nempty (n : Nat) : ExprLow String :=
  nproduct n empty (λ _ => empty)

def expected (n : Nat) : Type :=
  List.foldl (λ acc i => acc × Unit) Unit (List.range n)

def nemptyT (n : Nat) : Type := by
  precomputeTac [T| nempty n, ε] by
    dsimp [drunfold_defs, drcomponents]
    dsimp [ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module']
    unfold ExprLow.build_module'
