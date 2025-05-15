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

#reduce (types := true) List.foldl (λ acc i => acc × Unit) Unit (List.range 2)
#reduce (types := true) List.foldl (λ acc i => acc × Unit) Unit (List.range 3)

def PList (S : Type _) (n : Nat) : Type _ :=
  List.foldl (λ acc i => acc × S) S (List.range n)

theorem plist_concat.{u} {S : Type u} {n} :
  (PList.{u} S n × S) = PList.{u} S (n + 1) := by sorry

theorem plist_cons.{u} {S : Type u} {n} :
  (PList.{u} S n) = PList.{u} S (n + 1) := by sorry

theorem cast_module_type {I T T' : Type _} (heq : T = T') : Module I T = Module I T' := by subst T; rfl

def liftNL {S} (n : Nat) (m : Module String S) : Module String (PList S n) :=
  match n with
  | 0 => m
  | n+1 => (cast_module_type plist_concat).mp (liftNL n m).liftLM

theorem foldl_acc_build_module {l : List Nat} {e e' eb eb'} :
  (ExprLow.build_module' ε e) = .some eb →
  (ExprLow.build_module' ε e') = .some eb' →
  ExprLow.build_module ε (List.foldl (fun acc i => acc.product e) e' l)
  = List.foldl (fun acc i => ⟨ _, Module.product acc.2 (ExprLow.build_module ε e).2 ⟩) (ExprLow.build_module ε e') l := by
  induction l generalizing e' eb' with
  | nil => intros; rfl
  | cons x xs ih =>
    intro heb1 heb2
    dsimp; rw [ih]
    rotate_left 2
    dsimp [ExprLow.build_module']; rw [heb1, heb2]; dsimp
    rotate_left 1; assumption
    congr
    conv => lhs; dsimp [ExprLow.build_module, ExprLow.build_module']; rw [heb1, heb2]; dsimp
    unfold ExprLow.build_module
    congr
    all_goals solve | rw [heb2]; rfl | rw [heb1]; rfl

def nemptyT (n : Nat) : Type := by
  precomputeTac [T| nempty n, ε] by
    dsimp [drunfold_defs, drcomponents]
    dsimp [ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module']
