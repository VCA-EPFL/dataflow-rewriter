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

-- False
-- theorem plist_cons.{u} {S : Type u} {n} :
--   (PList.{u} S n) = PList.{u} S (n + 1) := by sorry

theorem cast_module_type {I T T' : Type _} (heq : T = T') : Module I T = Module I T' := by subst T; rfl

def liftNL {S} (n : Nat) (m : Module String S) : Module String (PList S n) :=
  match n with
  | 0 => m
  | n + 1 => (cast_module_type plist_concat).mp (liftNL n m).liftLM

theorem foldl_acc_build_module {α} {ε} {acc accb} {l : List α} {f : α → ExprLow String}:
  (∀ i, i ∈ l → ∃ b, (ExprLow.build_module' ε (f i)) = .some b) →
  (ExprLow.build_module' ε acc) = .some accb →
  ExprLow.build_module ε (List.foldl (λ acc i => acc.product (f i)) acc l)
  = List.foldl (λ acc i => ⟨_, Module.product acc.2 (ExprLow.build_module ε (f i)).2⟩) (ExprLow.build_module ε acc) l := by
  induction l generalizing acc accb with
  | nil => intros; rfl
  | cons x xs ih =>
    intro hfb haccb
    have Hxin: x ∈ x :: xs := by simpa
    obtain ⟨eb, heb⟩ := hfb x Hxin
    dsimp; rw [ih]
    rotate_left 2
    dsimp [ExprLow.build_module']; rw [heb, haccb]; dsimp
    rotate_left 1; intros i Hi
    apply hfb
    right; assumption
    congr
    conv => lhs; dsimp [ExprLow.build_module, ExprLow.build_module']; rw [heb, haccb]; dsimp
    unfold ExprLow.build_module
    congr
    all_goals solve | rw [haccb]; rfl | rw [heb]; rfl

-- TODO: good name
def dproduct {Ident} (a b : TModule1 Ident) : TModule1 Ident :=
  ⟨a.1 × b.1, Module.product a.2 b.2⟩

theorem dproduct_1 {Ident} (a b : TModule1 Ident) :
  (dproduct a b).1 = (a.1 × b.1) := by rfl

theorem foldl_acc_plist {Ident α} (acc : TModule1 Ident) (l : List α) (f : α → TModule1 Ident):
  ((List.foldl (λ acc i => ⟨acc.1 × (f i).1, Module.product acc.2 (f i).2⟩) acc l) : TModule1 Ident).1
  = (List.foldl (λ acc i => acc × (f i).1) acc.1 l) := by
    induction l generalizing acc with
    | nil => rfl
    | cons x xs ih =>
      dsimp
      conv =>
        pattern (Sigma.fst _ × Sigma.fst _)
        rw [←dproduct_1]
      rw [←ih (acc := dproduct acc (f x))]
      rfl

def nemptyT (n : Nat) : Type := by
  precomputeTac [T| nempty n, ε] by
    dsimp [drunfold_defs, drcomponents]
    dsimp [ExprLow.build_module_type]
    rw [foldl_acc_build_module]
    rotate_left 1
    intros i Hi
    dsimp [ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module']
    rw [empty_in_ε]
    simp (disch := simpa) only [toString, drcompute]
    apply Exists.intro _; rfl
    dsimp [ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module']
    simp only [drenv]
    dsimp
    rw [foldl_acc_plist]
    dsimp [ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module']
    simp only [drenv, drcompute]
    rw [←PList]
