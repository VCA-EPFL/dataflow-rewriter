/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Lean
import Leanses
import Qq

import DataflowRewriter.Basic
import DataflowRewriter.Simp
import DataflowRewriter.List
import DataflowRewriter.AssocList
import DataflowRewriter.HVector
import DataflowRewriter.Tactic
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Convert

open Batteries (AssocList)

namespace DataflowRewriter

/--
State that there exists zero or more internal rule executions to reach a final
state from an initial state.
-/
inductive existSR {S : Type _} (rules : List (S → S → Prop)) : S → S → Prop where
| done : ∀ init, existSR rules init init
| step : ∀ init mid final rule,
    rule ∈ rules →
    rule init mid →
    existSR rules mid final →
    existSR rules init final

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

section

universe i

variable {Ident : Type i}
variable [DecidableEq Ident]

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

def connect'' {Ti To S} (ruleO : S → To → S → Prop) (ruleI : S → Ti → S → Prop)
  -- (int : S → S → Prop)
  : S → S → Prop :=
  (λ st st' =>
     (∀ wf : To = Ti,
       ∃ consumed_output output, ruleO st output consumed_output
         -- ∧ int consumed_output consumed_input
         ∧ ruleI consumed_output (wf.mp output) st')
     ∧ (∀ nwf : To ≠ Ti, False))

/--
`connect'` will produce a new rule that fuses an input with an output, with a
precondition that the input and output type must match.
-/
@[drunfold] def connect' {S : Type _} (mod : Module Ident S) (o i : InternalPort Ident) : Module Ident S :=
  { inputs := mod.inputs.eraseAll i ,
    outputs :=  mod.outputs.eraseAll o,
    internals := connect'' (mod.outputs.getIO o).2 (mod.inputs.getIO i).2 -- (existSR mod.internals)
    :: mod.internals }

theorem connect''_dep_rw {C : Type} {x y x' y' : Σ (T : Type), C → T → C → Prop} (h : x' = x := by simp; rfl) (h' : y' = y := by simp; rfl) :
    @Module.connect'' y.1 x.1 C x.2 y.2 = @Module.connect'' y'.1 x'.1 C x'.2 y'.2 := by
  intros; subst_vars; rfl

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

@[drunfold] def mapInputPorts {S} (mod : Module Ident S) (f : InternalPort Ident → InternalPort Ident) : Module Ident S :=
  { mod with inputs := mod.inputs.mapKey f }

@[drunfold] def mapOutputPorts {S} (mod : Module Ident S) (f : InternalPort Ident → InternalPort Ident) : Module Ident S :=
  { mod with outputs := mod.outputs.mapKey f }

@[drunfold] def mapPorts {S} (mod : Module Ident S) (f : InternalPort Ident → InternalPort Ident) : Module Ident S :=
  mod.mapInputPorts f |>.mapOutputPorts f

@[drunfold] def mapPorts2 {S} (mod : Module Ident S) (f g : InternalPort Ident → InternalPort Ident) : Module Ident S :=
  mod.mapInputPorts f |>.mapOutputPorts g

def invertible {α} [DecidableEq α] (p : AssocList α α) : Prop :=
  p.keysList.inter p.inverse.keysList = ∅ ∧ p.keysList.Nodup ∧ p.inverse.keysList.Nodup

def bijectivePortRenaming (p : PortMap Ident (InternalPort Ident)) (i: InternalPort Ident) : InternalPort Ident :=
  let p' := p.inverse
  if p.keysList.inter p'.keysList = ∅ && p.keysList.Nodup && p'.keysList.Nodup then
    let map := p.append p.inverse
    map.find? i |>.getD i
  else i

theorem invertibleMap {α} [DecidableEq α] {p : AssocList α α} {a b} :
  invertible p →
  (p.append p.inverse).find? a = some b → (p.append p.inverse).find? b = some a := by sorry

theorem bijectivePortRenaming_bijective {p : PortMap Ident (InternalPort Ident)} :
  Function.Bijective (bijectivePortRenaming p) := by
  rw [Function.bijective_iff_existsUnique]
  intro b
  by_cases h : p.keysList.inter p.inverse.keysList = ∅ && p.keysList.Nodup && p.inverse.keysList.Nodup
  · cases h' : (p.append p.inverse).find? b
    · refine ⟨b, ?_, ?_⟩
      unfold bijectivePortRenaming; simp [*, -AssocList.find?_eq]
      unfold bijectivePortRenaming; simp [*, -AssocList.find?_eq]
      intro y Hy; simp at h; simp [h, -AssocList.find?_eq] at Hy
      cases h'' : AssocList.find? y (AssocList.append p (AssocList.inverse p))
      · rw [h''] at Hy; dsimp at Hy; assumption
      · rw [h''] at Hy; dsimp at Hy; subst b
        have := invertibleMap (by unfold invertible; simp [*]) h''
        rw [this] at h'; injection h'
    · rename_i val
      refine ⟨val, ?_, ?_⟩
      · unfold bijectivePortRenaming; simp [*, -AssocList.find?_eq];
        simp at h; simp [h, -AssocList.find?_eq]
        rw [invertibleMap]; rfl; simp [invertible, *]; assumption
      · unfold bijectivePortRenaming; simp [*, -AssocList.find?_eq]; intros y hY
        simp at h; simp [h, -AssocList.find?_eq] at hY
        cases h'' : AssocList.find? y (AssocList.append p (AssocList.inverse p))
        · rw [h''] at hY; dsimp at hY; subst y; rw [h''] at h'; injection h'
        · rename_i val'; rw [h''] at hY; dsimp at *; subst b
          have := invertibleMap (by simp [invertible, *]) h''; rw [this] at h'; injection h'
  · refine ⟨b, ?_, ?_⟩
    unfold bijectivePortRenaming; simp [*]; intro a b c; exfalso; apply h; simp [*]
    unfold bijectivePortRenaming; simp [*]; split; exfalso; apply h; simp [*]
    simp

def renamePorts {S} (m : Module Ident S) (p : PortMapping Ident) : Module Ident S :=
  m.mapPorts2 (bijectivePortRenaming p.input) (bijectivePortRenaming p.output)

-- theorem find?_inputs_left {S T} {mod1 : Module Ident S} {mod2 : Module Ident T} {ident rule} :
--   mod1.inputs.find? ident = some rule →
--   (mod1.product mod2).inputs.find? ident = some (liftL rule) := by sorry

-- theorem disjoint_find?_inputs_right {S T} {mod1 : Module Ident S} {mod2 : Module Ident T} {ident rule} :
--   ¬ mod1.inputs.contains ident →
--   mod2.inputs.find? ident = some rule →
--   (mod1.product mod2).inputs.find? ident = some (liftR rule) := by sorry

-- theorem find?_outputs_left {S T} {mod1 : Module Ident S} {mod2 : Module Ident T} {ident rule} :
--   mod1.outputs.find? ident = some rule →
--   (mod1.product mod2).outputs.find? ident = some (liftL rule) := by sorry

-- theorem find?_outputs_right {S T} {mod1 : Module Ident S} {mod2 : Module Ident T} {ident rule} :
--   ¬ mod1.outputs.contains ident →
--   mod2.outputs.find? ident = some rule →
--   (mod1.product mod2).outputs.find? ident = some (liftR rule) := by sorry

end

section

variable {Ident}
variable {S}

def toInterface (m : Module Ident S): Interface Ident :=
  ⟨m.inputs.keysList, m.outputs.keysList⟩

def toPortMapping (m : Module Ident S) (i : Ident) : PortMapping Ident :=
  m.toInterface.toPortMapping i

theorem mapInputPorts_id {m : Module Ident S} :
  m.mapInputPorts id = m := by
  unfold mapInputPorts
  rw [Batteries.AssocList.mapKey_toList]; simp

theorem mapOutputPorts_id {m : Module Ident S} :
  m.mapOutputPorts id = m := by
  unfold mapOutputPorts
  rw [Batteries.AssocList.mapKey_toList]; simp

variable [DecidableEq Ident]

theorem bijectivePortRenaming_id : bijectivePortRenaming (Ident := Ident) ∅ = id := by rfl

theorem renamePorts_empty {m : Module Ident S} :
  m.renamePorts ∅ = m := by
  unfold renamePorts
  have i : (∅ : PortMapping Ident).input = ∅ := by rfl
  have o : (∅ : PortMapping Ident).output = ∅ := by rfl
  rw [i,o]
  rw [bijectivePortRenaming_id]; unfold Module.mapPorts2; rw [mapInputPorts_id,mapOutputPorts_id]

def mapIdent {Ident Ident' T} (inpR outR: Ident → Ident') (m : Module Ident T)
 : Module Ident' T :=
  {
    inputs := m.inputs.mapKey (InternalPort.map inpR),
    outputs := m.outputs.mapKey (InternalPort.map outR),
    internals := m.internals
  }

end

end Module

structure Disjoint {Ident S T} [DecidableEq Ident] (mod1 : Module Ident S) (mod2 : Module Ident T) : Prop where
  inputs_disjoint : mod1.inputs.disjoint_keys mod2.inputs
  outputs_disjoint : mod1.outputs.disjoint_keys mod2.outputs

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
  inputs_present ident :
    (imod.inputs.find? ident).isSome = (smod.inputs.find? ident).isSome
  outputs_present ident :
    (imod.outputs.find? ident).isSome = (smod.outputs.find? ident).isSome
  input_types ident : (imod.inputs.getIO ident).1 = (smod.inputs.getIO ident).1
  output_types ident : (imod.outputs.getIO ident).1 = (smod.outputs.getIO ident).1

theorem MatchInterface_simpler {imod : Module Ident I} {smod : Module Ident S} :
  (∀ ident, (imod.inputs.mapVal (λ _ => Sigma.fst)).find? ident = (smod.inputs.mapVal (λ _ => Sigma.fst)).find? ident) →
  (∀ ident, (imod.outputs.mapVal (λ _ => Sigma.fst)).find? ident = (smod.outputs.mapVal (λ _ => Sigma.fst)).find? ident) →
  MatchInterface imod smod := by sorry

theorem MatchInterface_simpler2 {imod : Module Ident I} {smod : Module Ident S} {ident} :
  MatchInterface imod smod →
  (imod.inputs.mapVal (λ _ => Sigma.fst)).find? ident = (smod.inputs.mapVal (λ _ => Sigma.fst)).find? ident
  ∧ (imod.outputs.mapVal (λ _ => Sigma.fst)).find? ident = (smod.outputs.mapVal (λ _ => Sigma.fst)).find? ident := by sorry

theorem MatchInterface_simpler_iff {imod : Module Ident I} {smod : Module Ident S} :
  MatchInterface imod smod ↔
  (∀ ident, (imod.inputs.mapVal (λ _ => Sigma.fst)).find? ident = (smod.inputs.mapVal (λ _ => Sigma.fst)).find? ident
  ∧ (imod.outputs.mapVal (λ _ => Sigma.fst)).find? ident = (smod.outputs.mapVal (λ _ => Sigma.fst)).find? ident) := by
  constructor
  · intros; solve_by_elim [MatchInterface_simpler2]
  · intros ha; apply MatchInterface_simpler <;> intro ident <;> specializeAll ident
    · apply ha.left
    · apply ha.right

instance : MatchInterface (@Module.empty Ident S) (Module.empty I) :=
  ⟨ fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl ⟩

instance {m : Module Ident S} : MatchInterface m m :=
  ⟨ fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl ⟩

theorem MatchInterface_transitive {I J S} {imod : Module Ident I} {smod : Module Ident S} (jmod : Module Ident J) :
  MatchInterface imod jmod →
  MatchInterface jmod smod →
  MatchInterface imod smod := by
  intro ⟨ i, j, a, b ⟩ ⟨ k, w, c, d ⟩
  constructor <;> (try simp [*]; done) <;> (intros; simp only [*])

-- theorem MatchInterface_Disjoint {I J S K} {imod : Module Ident I} {smod : Module Ident S} {imod' : Module Ident J} {smod' : Module Ident K}
--   [MatchInterface imod smod]
--   [MatchInterface imod' smod'] :
--   Disjoint imod imod' →
--   Disjoint smod smod' := by sorry

instance MatchInterface_connect {I S} {o i} {imod : Module Ident I} {smod : Module Ident S}
         [mm : MatchInterface imod smod]
         : MatchInterface (imod.connect' o i) (smod.connect' o i) := by
  simp only [MatchInterface_simpler_iff] at *; intro ident; specializeAll ident
  rcases mm with ⟨mm1, mm2⟩
  dsimp [Module.connect']
  constructor
  · simp only [AssocList.eraseAll_map_comm]
    by_cases h : i = ident <;> subst_vars
    · simp only [AssocList.find?_eraseAll_eq]
    · simpa (disch := assumption) only [AssocList.find?_eraseAll_neq]
  · simp only [AssocList.eraseAll_map_comm]
    by_cases h : o = ident <;> subst_vars
    · simp only [AssocList.find?_eraseAll_eq]
    · simpa (disch := assumption) only [AssocList.find?_eraseAll_neq]

-- instance MatchInterface_mapInputPorts {I S} {o i} {imod : Module Ident I} {smod : Module Ident S}
--          [MatchInterface imod smod]
--          : MatchInterface (imod.mapInputPorts i) (smod.connect' o i) := by sorry

instance MatchInterface_product {I J S T} {imod : Module Ident I} {tmod : Module Ident T}
         {smod : Module Ident S} (jmod : Module Ident J) [MatchInterface imod tmod]
         [MatchInterface smod jmod] :
         MatchInterface (imod.product smod) (tmod.product jmod) := by sorry
  -- input_types := by
  --   rename_i inst1 inst2; intro ident; simp [Module.product]
  --   rcases inst1 with ⟨ inst1_in, _ ⟩
  --   rcases inst2 with ⟨ inst2_in, _ ⟩
  --   specialize inst1_in ident; specialize inst2_in ident
  --   by_cases h : ident ∈ imod.inputs.keysList
  --   · unfold PortMap.getIO at *
  --     apply Batteries.AssocList.keysList_find2 at h
  --     rw [Option.isSome_iff_exists] at h; rcases h with ⟨ val, hfind ⟩
  --     rw [Batteries.AssocList.append_find_left]
  --     all_goals sorry
  --   · sorry
  -- output_types := sorry

theorem match_interface_inputs_contains {I S} {imod : Module Ident I} {smod : Module Ident S}
  [MatchInterface imod smod] {k}:
  imod.inputs.contains k ↔ smod.inputs.contains k := by
  rcases ‹MatchInterface _ _› with ⟨a, b, c, d⟩
  simp only [←AssocList.contains_find?_isSome_iff]
  rw [a]

theorem match_interface_outputs_contains {I S} {imod : Module Ident I} {smod : Module Ident S}
  [MatchInterface imod smod] {k}:
  imod.outputs.contains k ↔ smod.outputs.contains k := by
  rcases ‹MatchInterface _ _› with ⟨a, b, c, d⟩
  simp only [←AssocList.contains_find?_isSome_iff]
  rw [b]

theorem MatchInterface_mapInputPorts {I S} {imod : Module Ident I}
         {smod : Module Ident S} [MatchInterface imod smod] {f} :
         Function.Bijective f →
         MatchInterface (imod.mapInputPorts f) (smod.mapInputPorts f) := by sorry

theorem MatchInterface_mapOutputPorts {I S} {imod : Module Ident I}
         {smod : Module Ident S} [MatchInterface imod smod] {f} :
         Function.Bijective f →
         MatchInterface (imod.mapOutputPorts f) (smod.mapOutputPorts f) := by sorry

end Match

theorem existSR_reflexive {S} {rules : List (S → S → Prop)} {s} :
  existSR rules s s := existSR.done s

theorem existSR_transitive {S} (rules : List (S → S → Prop)) :
  ∀ s₁ s₂ s₃,
    existSR rules s₁ s₂ →
    existSR rules s₂ s₃ →
    existSR rules s₁ s₃ := by
  intro s₁ s₂ s₃ He1 He2
  induction He1 generalizing s₃; assumption
  constructor; all_goals solve_by_elim

theorem existSR_append_left {S} (rules₁ rules₂ : List (S → S → Prop)) :
  ∀ s₁ s₂,
    existSR rules₁ s₁ s₂ →
    existSR (rules₁ ++ rules₂) s₁ s₂ := by
  intro s₁ s₂ hrule
  induction hrule with
  | done => constructor
  | step init mid final rule hrulein hrule hex =>
    apply existSR.step (rule := rule) (mid := mid) <;> simp [*]

theorem existSR_append_right {S} (rules₁ rules₂ : List (S → S → Prop)) :
  ∀ s₁ s₂,
    existSR rules₂ s₁ s₂ →
    existSR (rules₁ ++ rules₂) s₁ s₂ := by
  intro s₁ s₂ hrule
  induction hrule with
  | done => constructor
  | step init mid final rule hrulein hrule hex =>
    apply existSR.step (rule := rule) (mid := mid) <;> simp [*]

theorem existSR_liftL' {S T} (rules : List (S → S → Prop)) :
  ∀ s₁ s₂ (t₁ : T),
    existSR rules s₁ s₂ →
    existSR (rules.map Module.liftL') (s₁, t₁) (s₂, t₁) := by
  intro s₁ s₂ t₁ hrule
  induction hrule with
  | done => constructor
  | step init mid final rule hrulein hrule hex ih =>
    apply existSR.step (rule := @Module.liftL' S T rule) (mid := (mid, t₁)) <;> try assumption
    simp; exists rule
    simp [*, Module.liftL']

theorem existSR_liftR' {S T} (rules : List (S → S → Prop)) :
  ∀ s₁ s₂ (t₁ : T),
    existSR rules s₁ s₂ →
    existSR (rules.map Module.liftR') (t₁, s₁) (t₁, s₂) := by
  intro s₁ s₂ t₁ hrule
  induction hrule with
  | done => constructor
  | step init mid final rule hrulein hrule hex ih =>
    apply existSR.step (rule := @Module.liftR' T S rule) (mid := (t₁, mid)) <;> try assumption
    simp; exists rule
    simp [*, Module.liftR']

theorem existSR_cons {S} {r} {rules : List (S → S → Prop)} :
  ∀ s₁ s₂,
    existSR rules s₁ s₂ →
    existSR (r :: rules) s₁ s₂ := by
  intro s₁ s₂ hrule
  induction hrule with
  | done => constructor
  | step init mid final rule hrulein hrule hex ih =>
    constructor; right; assumption; assumption; assumption

namespace Module

section Refinementφ

variable {I : Type _}
variable {S : Type _}
variable {Ident : Type _}
variable [DecidableEq Ident]

variable (imod : Module Ident I)
variable (smod : Module Ident S)

variable [mm : MatchInterface imod smod]

/-
This could be made even more flexible by passing a custom type comparison
function for the inputs and outputs.  For now this might be general enough
though.
-/
structure indistinguishable (init_i : I) (init_s : S) : Prop where
  inputs_indistinguishable : ∀ (ident : InternalPort Ident) new_i v,
    (imod.inputs.getIO ident).2 init_i v new_i →
    ∃ new_s, (smod.inputs.getIO ident).2 init_s ((mm.input_types ident).mp v) new_s
  outputs_indistinguishable : ∀ ident new_i v,
    (imod.outputs.getIO ident).2 init_i v new_i →
    ∃ new_s, (smod.outputs.getIO ident).2 init_s ((mm.output_types ident).mp v) new_s

structure comp_refines (R : I → S → Prop) (init_i : I) (init_s : S) : Prop where
  inputs :
    ∀ ident mid_i v,
      (imod.inputs.getIO ident).2 init_i v mid_i →
      ∃ almost_mid_s mid_s,
        (smod.inputs.getIO ident).2 init_s ((mm.input_types ident).mp v) almost_mid_s
        ∧ existSR smod.internals almost_mid_s mid_s
        ∧ R mid_i mid_s
  outputs :
    ∀ ident mid_i v,
      (imod.outputs.getIO ident).2 init_i v mid_i →
      ∃ mid_s,
        (smod.outputs.getIO ident).2 init_s ((mm.output_types ident).mp v) mid_s
        ∧ R mid_i mid_s
  internals :
    ∀ rule mid_i,
      rule ∈ imod.internals →
      rule init_i mid_i →
      ∃ mid_s,
        existSR smod.internals init_s mid_s
        ∧ R mid_i mid_s

@[reducible] def cast_first {β : Type _ → Type _} {a b : (Σ α, β α)} (h : a = b) : a.fst = b.fst := by
  subst_vars; rfl

theorem rw_rule_execution {S : Type _} {a b : Σ (T : Type _), S → T → S → Prop} {s s'} {v : a.fst} (h : a = b) :
  a.snd s v s' ↔ b.snd s ((cast_first h).mp v) s' := by subst_vars; rfl

theorem rule_contains {S} {a : PortMap Ident (Σ T, S → T → S → Prop)} {ident init_i v new_i}:
  (a.getIO ident).2 init_i v new_i →
  a.contains ident := by
  unfold PortMap.getIO
  intro H
  cases h : (AssocList.find? ident a)
  · have : ((AssocList.find? ident a).getD ⟨PUnit.{u_3 + 1}, fun x x x => False⟩) = ⟨PUnit.{u_3 + 1}, fun x x x => False⟩ := by
      rw [h]; rfl
    rw [rw_rule_execution this] at H; simp at H
  · rw [← AssocList.contains_find?_iff]; tauto

theorem indistinguishable_reflexive i_init :
  indistinguishable imod imod i_init i_init := by
  constructor <;> (intros; solve_by_elim)

theorem indistinguishable_transitive {J} (jmod : Module Ident J)
        [MatchInterface imod jmod] [MatchInterface jmod smod] :
  ∀ i_init j_init s_init,
    indistinguishable imod jmod i_init j_init →
    indistinguishable jmod smod j_init s_init →
    indistinguishable imod smod i_init s_init := by
  intro i_init j_init s_init Hind₁ Hind₂
  rcases Hind₁ with ⟨ Hind₁_in, Hind₁_out ⟩
  rcases Hind₂ with ⟨ Hind₂_in, Hind₂_out ⟩
  stop constructor
  -- · intro ident new_i v Hcont Hrule

theorem indistinguishable_mapInputPorts
        [MatchInterface imod smod] {f i_init s_init} {h : Function.Bijective f} :
  have _ := MatchInterface_mapInputPorts (imod := imod) (smod := smod) h
  imod.indistinguishable smod i_init s_init →
  (imod.mapInputPorts f).indistinguishable (smod.mapInputPorts f) i_init s_init := by sorry

theorem indistinguishable_mapOutputPorts
        [MatchInterface imod smod] {f i_init s_init} {h : Function.Bijective f} :
  have _ := MatchInterface_mapOutputPorts (imod := imod) (smod := smod) h
  imod.indistinguishable smod i_init s_init →
  (imod.mapOutputPorts f).indistinguishable (smod.mapOutputPorts f) i_init s_init := by sorry

def refines_φ (R : I → S → Prop) :=
  ∀ (init_i : I) (init_s : S),
    R init_i init_s →
     comp_refines imod smod R init_i init_s

notation:35 x " ⊑_{" R:35 "} " y:34 => refines_φ x y R

theorem refines_φ_reflexive : imod ⊑_{Eq} imod := by
  intro init_i init_s heq; subst_vars
  constructor
  · intro ident mid_i v hrule
    refine ⟨ mid_i, mid_i, hrule, existSR.done _, rfl ⟩
  · intro ident mid_i v hrule
    refine ⟨ mid_i, hrule, rfl ⟩
  · intro ident mid_i hcont hrule
    refine ⟨ mid_i, ?_, rfl ⟩
    constructor <;> try assumption
    exact .done _

theorem refines_φ_multistep :
    ∀ φ, imod ⊑_{φ} smod →
    ∀ i_init s_init,
      φ i_init s_init →
      ∀ i_mid, existSR imod.internals i_init i_mid →
      ∃ s_mid,
        existSR smod.internals s_init s_mid
        ∧ φ i_mid s_mid := by
  intros φ Href i_init s_init Hphi i_mid Hexist
  induction Hexist generalizing s_init
  · exists s_init; tauto
  · rename I → I → Prop => rule
    rename ∀ _, _ => iH
    unfold refines_φ at Href
    rcases Href _ _ Hphi with ⟨ Hinp, Hout, Hint ⟩
    rcases Hint _ _ ‹_› ‹_› with ⟨ s_mid, Hexist, Hphi' ⟩
    rcases iH _ Hphi' with ⟨ s_mid', Hexists, Hphi ⟩
    exists s_mid'
    all_goals solve_by_elim [existSR_transitive]

theorem refines_φ_transitive {J} (smod' : Module Ident J) {φ₁ φ₂}
  [MatchInterface imod smod']
  [MatchInterface smod' smod]:
    imod ⊑_{φ₁} smod' →
    smod' ⊑_{φ₂} smod →
    imod ⊑_{fun a b => ∃ c, φ₁ a c ∧ φ₂ c b} smod := by
  intros h1 h2
  intro init_i init_s HR
  rcases HR with ⟨ init_j, Hφ₁, Hφ₂ ⟩
  rcases h1 _ _ Hφ₁ with ⟨ h1inp, h1out, h1int ⟩
  rcases h2 _ _ Hφ₂ with ⟨ h2inp, h2out, h2int ⟩
  constructor
  · clear h1out h1int h2out h2int
    intro ident mid_i v Hrule
    specialize h1inp _ _ _ Hrule
    rcases h1inp with ⟨ mid_mid_j, mid_j, hrule₁, hexists₁, hphi₁ ⟩
    specialize h2inp _ _ _ hrule₁
    rcases h2inp with ⟨ mid_mid_s, mid_s, hrule₂, hexists₂, hphi₂ ⟩
    rcases refines_φ_multistep _ _ _ h2 _ _ hphi₂ _ hexists₁ with ⟨ mid_s₃, hexists₃, hphi₃ ⟩
    refine ⟨ ?_, mid_s₃, ?inp.and1, ?inp.and2, mid_j, ?_, ?_ ⟩
    case and1 => convert hrule₂; simp
    case and2 => solve_by_elim [existSR_transitive]
    all_goals assumption
  · clear h1inp h1int h2inp h2int
    intro ident mid_i v Hrule
    specialize h1out _ _ _ Hrule
    rcases h1out with ⟨ mid_j, hrule₁, hphi₁ ⟩
    specialize h2out _ _ _ hrule₁
    rcases h2out with ⟨ mid_s, hrule₂, hphi₂ ⟩;
    exists mid_s; and_intros; convert hrule₂; simp; tauto
    -- rcases refines_φ_multistep _ _ _ h2 _ _ hphi₂ _ hexists₁ with ⟨ mid_s₃, hexists₃, hphi₃ ⟩
    -- refine ⟨ ?_, mid_s₃, ?out.and1, ?out.and2, mid_j, ?_, ?_ ⟩
    -- case and1 => convert hrule₂; simp
    -- case and2 => solve_by_elim [existSR_transitive]
    -- all_goals assumption
  · clear h1inp h1out h2inp h2out
    intro rule mid_i ruleIn Hrule
    specialize h1int rule mid_i ruleIn Hrule
    rcases h1int with ⟨ mid_j, hexist₁, hphi₁ ⟩
    have Href := refines_φ_multistep _ _ _ h2 _ _ Hφ₂ _ hexist₁
    rcases Href with ⟨ mid_s, hexist₂, hphi₂ ⟩
    refine ⟨ mid_s, hexist₂, ?_, by exact hphi₁, by exact hphi₂ ⟩

end Refinementφ

section Refinement

variable {I : Type _}
variable {S : Type _}
variable {Ident : Type _}
variable [DecidableEq Ident]

variable (imod : Module Ident I)
variable (smod : Module Ident S)

def refines :=
  ∃ (mm : MatchInterface imod smod) (R : I → S → Prop),
    imod ⊑_{fun x y => indistinguishable imod smod x y ∧ R x y} smod

def refines' :=
  ∃ (mm : MatchInterface imod smod) (R : I → S → Prop),
    (imod ⊑_{fun x y => R x y} smod)
    ∧ (∀ x y, R x y → indistinguishable imod smod x y)

notation:35 x " ⊑ " y:34 => refines x y
notation:35 x " ⊑' " y:34 => refines' x y

variable {imod smod}

theorem refines_φ_refines [MatchInterface imod smod] {φ} :
  (∀ i_init s_init, φ i_init s_init → indistinguishable imod smod i_init s_init) →
  imod ⊑_{φ} smod →
  imod ⊑ smod := by
  intro Hind Href
  exists inferInstance, φ
  intro init_i init_s ⟨ Hphi, Hindis ⟩
  specialize Href init_i init_s Hindis
  rcases Href with ⟨ Hin, Hout, Hint ⟩; constructor
  · intro ident mid_i v Hrule
    specialize Hin ident mid_i v Hrule
    tauto
  · intro ident mid_i v Hrule
    specialize Hout ident mid_i v Hrule
    tauto
  · intro rule mid_i Hcont Hrule
    specialize Hint rule mid_i Hcont Hrule
    tauto

theorem refines_refines' :
  imod ⊑ smod →
  imod ⊑' smod := by
  intro href
  rcases href with ⟨mm, R, href⟩
  refine ⟨mm, fun x y => imod.indistinguishable smod x y ∧ R x y, ?_, ?_⟩
  · assumption
  · simp +contextual

theorem refines'_refines :
  imod ⊑' smod →
  imod ⊑ smod := by
  intro href
  rcases href with ⟨mm, R, href, hind⟩
  solve_by_elim [refines_φ_refines]

theorem refines'_refines_iff :
  imod ⊑' smod ↔ imod ⊑ smod := by
  solve_by_elim [refines'_refines, refines_refines']

theorem refines_reflexive : imod ⊑ imod := by
  apply refines_φ_refines (φ := Eq) (smod := imod)
  intros; subst_vars; apply indistinguishable_reflexive
  apply refines_φ_reflexive

theorem refines_transitive {J} (imod' : Module Ident J):
    imod ⊑ imod' →
    imod' ⊑ smod →
    imod ⊑ smod := by
  intro h1 h2
  rcases h1 with ⟨ mm1, R1, h1 ⟩
  rcases h2 with ⟨ mm2, R2, h2 ⟩
  have mm3 := MatchInterface_transitive imod' mm1 mm2
  constructor <;> try assumption
  exists (fun a b => ∃ c, (imod.indistinguishable imod' a c ∧ R1 a c)
                        ∧ (imod'.indistinguishable smod c b ∧ R2 c b)); dsimp
  have : (fun x y => imod.indistinguishable smod x y ∧
             ∃ c, (imod.indistinguishable imod' x c ∧ R1 x c)
                ∧ (imod'.indistinguishable smod c y ∧ R2 c y))
           = (fun x y => ∃ c, (fun x y => imod.indistinguishable imod' x y ∧ R1 x y) x c
                            ∧ (fun x y => imod'.indistinguishable smod x y ∧ R2 x y) c y) := by
    ext x y
    constructor; tauto
    intro ⟨ c, ha, hb ⟩
    constructor; rotate_left; tauto
    apply indistinguishable_transitive imod smod imod' <;> tauto
  rw [this]
  apply refines_φ_transitive imod smod imod'
  assumption; assumption

theorem indistinguishability_product {J K} {i i₂ s s₂} {imod₂ : Module Ident J} {smod₂ : Module Ident K}
  [MatchInterface imod smod]
  [MatchInterface imod₂ smod₂] :
  imod.indistinguishable smod i s →
  imod₂.indistinguishable smod₂ i₂ s₂ →
  (imod.product imod₂).indistinguishable (smod.product smod₂) (i, i₂) (s, s₂) := by sorry

theorem indistinguishability_connect {i s inp out} [MatchInterface imod smod] :
  imod.indistinguishable smod i s →
  (imod.connect' out inp).indistinguishable (smod.connect' out inp) i s := by sorry

-- theorem rw_rule_execution' {S : Type _} {a b c : Σ (T : Type _), S → T → S → Prop} {s s'} {v : b.fst} (h : b.fst = a.fst) (h' : a = b) :
--   a.snd s (h.mp v) s' ↔ b.snd s (h'.mp (h' ▸ v)) s' := by subst_vars; rfl

-- theorem rw_rule_execution2 {S : Type _} {a b : Σ (T : Type _), S → T → S → Prop} {s s'} {v : a.fst} (h : a.fst = b.fst) :
--   a.snd s v s' ↔ a.snd s (h.mp v) s' := by
--     rcases a with ⟨a₁, a₂⟩
--     rcases b with ⟨b₁, b₂⟩
--     dsimp at *
--     simp at h;

theorem liftL'_rule_eq {A B} {rule' init_i init_i₂ mid_i₁ mid_i₂}:
  @liftL' A B rule' (init_i, init_i₂) (mid_i₁, mid_i₂) →
  rule' init_i mid_i₁ ∧ init_i₂ = mid_i₂ := by simp [liftL']

theorem liftR'_rule_eq {A B} {rule' init_i init_i₂ mid_i₁ mid_i₂}:
  @liftR' A B rule' (init_i, init_i₂) (mid_i₁, mid_i₂) →
  rule' init_i₂ mid_i₂ ∧ init_i = mid_i₁ := by simp [liftR']

theorem refines_φ_product {J K} {imod₂ : Module Ident J} {smod₂ : Module Ident K}
  [MatchInterface imod smod]
  [MatchInterface imod₂ smod₂] {φ₁ φ₂} :
    imod ⊑_{φ₁} smod →
    imod₂ ⊑_{φ₂} smod₂ →
    imod.product imod₂ ⊑_{λ a b => φ₁ a.1 b.1 ∧ φ₂ a.2 b.2} smod.product smod₂ := by
  intro href₁ href₂
  have mm_prod : MatchInterface (imod.product imod₂) (smod.product smod₂) := inferInstance
  unfold refines_φ at *
  intro ⟨init_i, init_i₂⟩ ⟨init_s,init_s₂⟩ hφ
  specialize href₁ init_i init_s hφ.left
  specialize href₂ init_i₂ init_s₂ hφ.right
  constructor
  · intro ident ⟨mid_i, mid_i₂⟩ hgetio hrule
    have hcontains := rule_contains hrule
    rcases Option.isSome_iff_exists.mp (AssocList.contains_some hcontains) with ⟨rule, hruleIn⟩
    rcases AssocList.append_find?2 hruleIn with hruleIn' | hruleIn'
    case inl =>
      rw [AssocList.find?_mapVal] at hruleIn'
      cases h : AssocList.find? ident imod.inputs; rw [h] at hruleIn'; injection hruleIn'
      rename_i rule'; rw [h] at hruleIn'; simp at hruleIn'; subst_vars
      have cast2 : ((imod.product imod₂).inputs.getIO ident).fst = (imod.inputs.getIO ident).fst := by
        dsimp [PortMap.getIO]; rw [hruleIn,h,liftL]; rfl
      have cast_rule : (imod.product imod₂).inputs.getIO ident = liftL (imod.inputs.getIO ident) := by
        dsimp [PortMap.getIO]; rw [hruleIn,h]; rfl
      rw [rw_rule_execution cast_rule] at hrule
      dsimp [liftL] at hrule; rcases hrule with ⟨hrule⟩; subst_vars
      rcases href₁ with ⟨href_in, href_out, href_int⟩
      clear href_out href_int
      have hcontains₂ : AssocList.contains ident imod.inputs := by
        apply AssocList.contains_some2; rw [h]; rfl
      have hrule₂ : (imod.inputs.getIO ident).snd init_i (cast2.mp hgetio) mid_i := by
        have : imod.inputs.getIO ident = rule' := by
          dsimp [PortMap.getIO]; rw [h]; rfl
        rw [rw_rule_execution this]
        simp; convert hrule; exact this.symm
        simp [cast]
      specialize href_in ident mid_i (cast2.mp hgetio) hrule₂
      rcases href_in with ⟨almost_mid_s, mid_s, hrule₃, hexists, hφ₃⟩
      refine ⟨ (almost_mid_s, ‹_›), (mid_s, ‹_›), ?_, ?_, ?_, ?_ ⟩
      · have : ∃ y, smod.inputs.find? ident = some y := by
          have := ‹MatchInterface imod smod›.inputs_present ident
          rw [h] at this
          simp [-AssocList.find?_eq] at this
          exact Option.isSome_iff_exists.mp this
        rcases this with ⟨Srule, HSrule⟩
        have : (AssocList.mapVal (fun x => liftL) smod.inputs).find? ident = some (@liftL _ K Srule) := by
          rw [←AssocList.find?_map_comm]; rw [HSrule]; rfl
        have s : (smod.product smod₂).inputs.getIO ident = liftL (smod.inputs.getIO ident) := by
          skip; dsimp [Module.product, PortMap.getIO]; rw [AssocList.append_find_left this]
          rw [HSrule]; rfl
        rw [rw_rule_execution s]
        dsimp [liftL]; refine ⟨?_, rfl⟩; convert hrule₃; simp
      · solve_by_elim [existSR_append_left, existSR_liftL']
      · assumption
      · apply hφ.right
    case inr =>
      rcases hruleIn' with ⟨hruleIn'none, hruleIn'⟩
      rw [AssocList.find?_mapVal] at hruleIn'
      cases h : AssocList.find? ident imod₂.inputs; rw [h] at hruleIn'; injection hruleIn'
      rename_i rule'; rw [h] at hruleIn'; simp at hruleIn'; subst_vars
      have cast2 : ((imod.product imod₂).inputs.getIO ident).fst = (imod₂.inputs.getIO ident).fst := by
        dsimp [PortMap.getIO]; rw [hruleIn,h,liftR]; rfl
      have cast_rule : (imod.product imod₂).inputs.getIO ident = liftR (imod₂.inputs.getIO ident) := by
        dsimp [PortMap.getIO]; rw [hruleIn,h]; rfl
      rw [rw_rule_execution cast_rule] at hrule
      dsimp [liftL] at hrule; rcases hrule with ⟨hrule⟩; subst_vars
      rcases href₂ with ⟨href_in, href_out, href_int⟩
      clear href_out href_int
      have hcontains₂ : AssocList.contains ident imod₂.inputs := by
        apply AssocList.contains_some2; rw [h]; rfl
      have hrule₂ : (imod₂.inputs.getIO ident).snd init_i₂ (cast2.mp hgetio) mid_i₂ := by
        have : imod₂.inputs.getIO ident = rule' := by
          dsimp [PortMap.getIO]; rw [h]; rfl
        rw [rw_rule_execution this]
        simp; convert hrule; exact this.symm
        simp [cast]
      specialize href_in ident mid_i₂ (cast2.mp hgetio) hrule₂
      rcases href_in with ⟨almost_mid_s, mid_s, hrule₃, hexists, hφ₃⟩
      refine ⟨ (‹_›, almost_mid_s), (‹_›, mid_s), ?_, ?_, ?_, ?_ ⟩
      · have : ∃ y, smod₂.inputs.find? ident = some y := by
          have := ‹MatchInterface imod₂ smod₂›.inputs_present ident
          rw [h] at this
          simp [-AssocList.find?_eq] at this
          exact Option.isSome_iff_exists.mp this
        rcases this with ⟨Srule, HSrule⟩
        have : smod.inputs.find? ident = none := by
          have := ‹MatchInterface imod smod›.inputs_present ident
          rw [AssocList.find?_mapVal] at hruleIn'none
          cases h : AssocList.find? ident imod.inputs; rw [h] at hruleIn'none
          rw [h] at this; simp [-AssocList.find?_eq] at this; assumption
          rw [h] at this; rw [h] at hruleIn'none; injection hruleIn'none
        have hrule_another : (AssocList.mapVal (fun x => @liftL S K) smod.inputs).find? ident = none := by
          rw [←AssocList.find?_map_comm]; simp only [*]; rfl
        have : (AssocList.mapVal (fun x => liftR) smod₂.inputs).find? ident = some (@liftR S _ Srule) := by
          rw [←AssocList.find?_map_comm]; rw [HSrule]; rfl
        have s : (smod.product smod₂).inputs.getIO ident = liftR (smod₂.inputs.getIO ident) := by
          skip; dsimp [Module.product, PortMap.getIO];
          rw [AssocList.append_find_right, this]
          · rw [HSrule]; rfl
          · rw [hrule_another]
        rw [rw_rule_execution s]
        dsimp [liftL]; refine ⟨?_, rfl⟩; convert hrule₃; simp
      · solve_by_elim [existSR_append_right, existSR_liftR']
      · apply hφ.left
      · assumption
  · intro ident ⟨mid_i, mid_i₂⟩ hgetio hrule
    have hcontains := rule_contains hrule
    rcases Option.isSome_iff_exists.mp (AssocList.contains_some hcontains) with ⟨rule, hruleIn⟩
    rcases AssocList.append_find?2 hruleIn with hruleIn' | hruleIn'
    case inl =>
      rw [AssocList.find?_mapVal] at hruleIn'
      cases h : AssocList.find? ident imod.outputs; rw [h] at hruleIn'; injection hruleIn'
      rename_i rule'; rw [h] at hruleIn'; simp at hruleIn'; subst_vars
      have cast2 : ((imod.product imod₂).outputs.getIO ident).fst = (imod.outputs.getIO ident).fst := by
        dsimp [PortMap.getIO]; rw [hruleIn,h,liftL]; rfl
      have cast_rule : (imod.product imod₂).outputs.getIO ident = liftL (imod.outputs.getIO ident) := by
        dsimp [PortMap.getIO]; rw [hruleIn,h]; rfl
      rw [rw_rule_execution cast_rule] at hrule
      dsimp [liftL] at hrule; rcases hrule with ⟨hrule⟩; subst_vars
      rcases href₁ with ⟨href_in, href_out, href_int⟩
      clear href_in href_int
      have hcontains₂ : AssocList.contains ident imod.outputs := by
        apply AssocList.contains_some2; rw [h]; rfl
      have hrule₂ : (imod.outputs.getIO ident).snd init_i (cast2.mp hgetio) mid_i := by
        have : imod.outputs.getIO ident = rule' := by
          dsimp [PortMap.getIO]; rw [h]; rfl
        rw [rw_rule_execution this]
        simp; convert hrule; exact this.symm
        simp [cast]
      specialize href_out ident mid_i (cast2.mp hgetio) hrule₂
      rcases href_out with ⟨mid_s, hrule₃, hφ₃⟩
      refine ⟨ (mid_s, ‹_›), ?_, ?_, ?_ ⟩
      · have : ∃ y, smod.outputs.find? ident = some y := by
          have := ‹MatchInterface imod smod›.outputs_present ident
          rw [h] at this
          simp [-AssocList.find?_eq] at this
          exact Option.isSome_iff_exists.mp this
        rcases this with ⟨Srule, HSrule⟩
        have : (AssocList.mapVal (fun x => liftL) smod.outputs).find? ident = some (@liftL _ K Srule) := by
          rw [←AssocList.find?_map_comm]; rw [HSrule]; rfl
        have s : (smod.product smod₂).outputs.getIO ident = liftL (smod.outputs.getIO ident) := by
          skip; dsimp [Module.product, PortMap.getIO]; rw [AssocList.append_find_left this]
          rw [HSrule]; rfl
        rw [rw_rule_execution s]
        dsimp [liftL]; refine ⟨?_, rfl⟩; convert hrule₃; simp
      · assumption
      · apply hφ.right
    case inr =>
      rcases hruleIn' with ⟨hruleIn'none, hruleIn'⟩
      rw [AssocList.find?_mapVal] at hruleIn'
      cases h : AssocList.find? ident imod₂.outputs; rw [h] at hruleIn'; injection hruleIn'
      rename_i rule'; rw [h] at hruleIn'; simp at hruleIn'; subst_vars
      have cast2 : ((imod.product imod₂).outputs.getIO ident).fst = (imod₂.outputs.getIO ident).fst := by
        dsimp [PortMap.getIO]; rw [hruleIn,h,liftR]; rfl
      have cast_rule : (imod.product imod₂).outputs.getIO ident = liftR (imod₂.outputs.getIO ident) := by
        dsimp [PortMap.getIO]; rw [hruleIn,h]; rfl
      rw [rw_rule_execution cast_rule] at hrule
      dsimp [liftL] at hrule; rcases hrule with ⟨hrule⟩; subst_vars
      rcases href₂ with ⟨href_in, href_out, href_int⟩
      clear href_in href_int
      have hcontains₂ : AssocList.contains ident imod₂.outputs := by
        apply AssocList.contains_some2; rw [h]; rfl
      have hrule₂ : (imod₂.outputs.getIO ident).snd init_i₂ (cast2.mp hgetio) mid_i₂ := by
        have : imod₂.outputs.getIO ident = rule' := by
          dsimp [PortMap.getIO]; rw [h]; rfl
        rw [rw_rule_execution this]
        simp; convert hrule; exact this.symm
        simp [cast]
      specialize href_out ident mid_i₂ (cast2.mp hgetio) hrule₂
      rcases href_out with ⟨mid_s, hrule₃, hφ₃⟩
      refine ⟨ (‹_›, mid_s), ?_, ?_, ?_ ⟩
      · have : ∃ y, smod₂.outputs.find? ident = some y := by
          have := ‹MatchInterface imod₂ smod₂›.outputs_present ident
          rw [h] at this
          simp [-AssocList.find?_eq] at this
          exact Option.isSome_iff_exists.mp this
        rcases this with ⟨Srule, HSrule⟩
        have : smod.outputs.find? ident = none := by
          have := ‹MatchInterface imod smod›.outputs_present ident
          rw [AssocList.find?_mapVal] at hruleIn'none
          cases h : AssocList.find? ident imod.outputs; rw [h] at hruleIn'none
          rw [h] at this; simp [-AssocList.find?_eq] at this; assumption
          rw [h] at this; rw [h] at hruleIn'none; injection hruleIn'none
        have hrule_another : (AssocList.mapVal (fun x => @liftL S K) smod.outputs).find? ident = none := by
          rw [←AssocList.find?_map_comm]; simp only [*]; rfl
        have : (AssocList.mapVal (fun x => liftR) smod₂.outputs).find? ident = some (@liftR S _ Srule) := by
          rw [←AssocList.find?_map_comm]; rw [HSrule]; rfl
        have s : (smod.product smod₂).outputs.getIO ident = liftR (smod₂.outputs.getIO ident) := by
          skip; dsimp [Module.product, PortMap.getIO];
          rw [AssocList.append_find_right, this]
          · rw [HSrule]; rfl
          · rw [hrule_another]
        rw [rw_rule_execution s]
        dsimp [liftL]; refine ⟨?_, rfl⟩; convert hrule₃; simp
      · apply hφ.left
      · assumption
  · intro rule ⟨mid_i₁, mid_i₂⟩ hruleIn hRule
    dsimp [Module.product, PortMap.getIO] at hruleIn
    simp at hruleIn
    rcases hruleIn with ⟨ rule', hruleIn, hruleEq ⟩ | ⟨ rule', hruleIn, hruleEq ⟩ <;> subst_vars
    · rcases href₁ with ⟨href_in, href_out, href_int⟩; clear href_in href_out
      obtain ⟨a, b⟩ := liftL'_rule_eq hRule; subst_vars
      specialize href_int _ mid_i₁ hruleIn a
      rcases href_int with ⟨mid_s, Hexists, hphi⟩
      apply Exists.intro (_, _); and_intros
      · dsimp [Module.product]; solve_by_elim [existSR_append_left, existSR_liftL']
      · assumption
      · apply hφ.right
    · rcases href₂ with ⟨href_in, href_out, href_int⟩; clear href_in href_out
      obtain ⟨a, b⟩ := liftR'_rule_eq hRule; subst_vars
      specialize href_int _ mid_i₂ hruleIn a
      rcases href_int with ⟨mid_s, Hexists, hphi⟩
      apply Exists.intro (_, _); and_intros
      · dsimp [Module.product]; solve_by_elim [existSR_append_right, existSR_liftR']
      · apply hφ.left
      · assumption

theorem refines'_product {J K} (imod₂ : Module Ident J) (smod₂ : Module Ident K):
    imod ⊑' smod →
    imod₂ ⊑' smod₂ →
    imod.product imod₂ ⊑' smod.product smod₂ := by
  intro href₁ href₂
  rcases href₁ with ⟨_, R, ref, ind⟩
  rcases href₂ with ⟨_, R2, ref₂, ind₂⟩
  refine ⟨ inferInstance, (λ a b => R a.1 b.1 ∧ R2 a.2 b.2), ?_ ⟩
  and_intros
  · apply refines_φ_product <;> assumption
  · intro _ _ ⟨Hrl, Hrr⟩
    specialize ind _ _ Hrl
    specialize ind₂ _ _ Hrr
    solve_by_elim [indistinguishability_product]

theorem refines_product {J K} (imod₂ : Module Ident J) (smod₂ : Module Ident K):
    imod ⊑ smod →
    imod₂ ⊑ smod₂ →
    imod.product imod₂ ⊑ smod.product smod₂ := by
  simp [←refines'_refines_iff]; apply refines'_product

theorem refines_φ_connect [MatchInterface imod smod] {φ i o} :
    -- (imod.outputs.getIO o).1 = (imod.inputs.getIO i).1 →
    -- imod.outputs.contains o →
    -- imod.inputs.contains i →
    imod ⊑_{φ} smod →
    imod.connect' o i ⊑_{φ} smod.connect' o i := by
  -- intro -- HEQ houtcont hincont
  intro href
  unfold refines_φ at *
  intro init_i init_s hphi
  constructor
  · specialize href _ _ hphi
    rcases href with ⟨href_in, href_out, href_int⟩
    clear href_out href_int
    intro ident mid_i v hrule
    have hcont := rule_contains hrule
    rcases Option.isSome_iff_exists.mp (AssocList.contains_some hcont) with ⟨rule, hruleIn⟩
    dsimp [Module.connect'] at hcont hruleIn; have hcont' := AssocList.contains_eraseAll hcont
    have getIO_eq : (imod.connect' o i).inputs.getIO ident = imod.inputs.getIO ident := by
      dsimp [Module.connect', PortMap.getIO]; rw [hruleIn, AssocList.find?_eraseAll hruleIn]
    specialize href_in ident mid_i ((cast_first getIO_eq).mp v) ((rw_rule_execution getIO_eq).mp hrule)
    rcases href_in with ⟨a_mid_s, mid_s, hrule_s, hexists, hphi'⟩
    have : AssocList.contains ident ((smod.connect' o i).inputs) := by
      rwa [← match_interface_inputs_contains (imod := imod.connect' o i)]
    have : ((smod.connect' o i).inputs.getIO ident) = (smod.inputs.getIO ident) := by
      dsimp [connect', PortMap.getIO] at *
      simp only [←AssocList.contains_find?_iff] at this
      rcases this with ⟨x, hin⟩
      rw [hin, AssocList.find?_eraseAll hin]
    refine ⟨a_mid_s, mid_s, ?_, ?_, ?_⟩
    · rw [rw_rule_execution this]; convert hrule_s; simp
    · apply existSR_cons; assumption
    · assumption
  · specialize href _ _ hphi
    rcases href with ⟨href_in, href_out, href_int⟩
    clear href_in href_int
    intro ident mid_i v hrule
    have hcont := rule_contains hrule
    rcases Option.isSome_iff_exists.mp (AssocList.contains_some hcont) with ⟨rule, hruleIn⟩
    dsimp [Module.connect'] at hcont hruleIn; have hcont' := AssocList.contains_eraseAll hcont
    have getIO_eq : (imod.connect' o i).outputs.getIO ident = imod.outputs.getIO ident := by
      dsimp [Module.connect', PortMap.getIO]; rw [hruleIn, AssocList.find?_eraseAll hruleIn]
    specialize href_out ident mid_i ((cast_first getIO_eq).mp v) ((rw_rule_execution getIO_eq).mp hrule)
    rcases href_out with ⟨mid_s, hrule_s, hphi'⟩
    have : AssocList.contains ident ((smod.connect' o i).outputs) := by
      rwa [← match_interface_outputs_contains (imod := imod.connect' o i)]
    have : ((smod.connect' o i).outputs.getIO ident) = (smod.outputs.getIO ident) := by
      dsimp [connect', PortMap.getIO] at *
      simp only [←AssocList.contains_find?_iff] at this
      rcases this with ⟨x, hin⟩
      rw [hin, AssocList.find?_eraseAll hin]
    refine ⟨mid_s, ?_, ?_⟩
    · rw [rw_rule_execution this]; convert hrule_s; simp
    -- · apply existSR_cons; assumption
    · assumption
  · intro rule mid_i hrulein hrule
    dsimp [connect', connect''] at hrulein
    cases hrulein
    -- · have : (smod.outputs.getIO o).fst = (smod.inputs.getIO i).fst := by
    unfold connect'' at hrule
    rcases Classical.em ((imod.outputs.getIO o).fst = (imod.inputs.getIO i).fst) with HEQ | HEQ
    · rcases hrule with ⟨hrule, _⟩
      rcases hrule HEQ with ⟨cons, outp, hrule1, hrule2⟩
      rcases href init_i init_s ‹_› with ⟨h1, hout, h2⟩; clear h1 h2
      specialize hout o cons outp ‹_›
      rcases hout with ⟨mid_s_o, hrule_s_o, hphi_o⟩
      specialize href _ _ hphi_o
      rcases href with ⟨href_in, h1, h2⟩; clear h1 h2
      specialize href_in i mid_i (HEQ.mp outp) ‹_›
      rcases href_in with ⟨alm_mid_s, mid_s_i, instep, exstep, hphi_i⟩
      exists mid_s_i; and_intros <;> try assumption
      apply existSR_transitive;
      · unfold connect'; dsimp; apply existSR.step; constructor; unfold connect'';
        and_intros; intros
        · constructor; constructor; and_intros
          · assumption
          · convert instep; simp
        · intro h; exfalso; apply h;
          rw [← ‹MatchInterface imod smod›.input_types]
          rw [← ‹MatchInterface imod smod›.output_types]
          assumption
        · apply existSR.done
      · unfold connect'; dsimp
        apply existSR_cons; assumption
    · rcases hrule with ⟨_, hrule⟩
      cases hrule HEQ
    · specialize href _ _ hphi; rcases href with ⟨h1, h2, href⟩; clear h1 h2
      specialize href _ _ ‹_› hrule
      rcases href with ⟨mid_s, h1, h2⟩
      exists mid_s; solve_by_elim [existSR_cons]

theorem refines'_connect {o i} :
    imod ⊑' smod →
    imod.connect' o i ⊑' smod.connect' o i := by
  intro href₁
  rcases href₁ with ⟨_, R, ref, ind⟩
  unfold refines' at *
  refine ⟨inferInstance, R, ?_, ?_⟩
  · intro init_i init_s hphi
    solve_by_elim [refines_φ_connect]
  · intro x y hphi; specialize ind _ _ hphi
    solve_by_elim [indistinguishability_connect]

theorem refines_connect {o i} :
    imod ⊑ smod →
    imod.connect' o i ⊑ smod.connect' o i := by
  simp [←refines'_refines_iff]; apply refines'_connect

theorem refines_φ_mapInputPorts {I S} {imod : Module Ident I} {smod : Module Ident S}
  [MatchInterface imod smod] {f φ} {h : Function.Bijective f} :
  have _ := MatchInterface_mapInputPorts (imod := imod) (smod := smod) h
  imod ⊑_{φ} smod →
  imod.mapInputPorts f ⊑_{φ} smod.mapInputPorts f := by
  intro hinj href
  unfold refines_φ at *
  intro init_i init_s hphi
  specialize href _ _ hphi
  constructor
  · rcases href with ⟨hinp, h1, h2⟩; clear h1 h2
    intro ident mid_i v hrule
    have := Function.bijective_iff_existsUnique f |>.mp h ident
    rcases this with ⟨ident', mapIdent, uniq⟩
    subst ident
    have : (imod.mapInputPorts f).inputs.getIO (f ident') = imod.inputs.getIO ident' := by
      unfold mapInputPorts PortMap.getIO; dsimp
      rw [AssocList.mapKey_find?]; exact h.injective
    have hrule' := (rw_rule_execution this).mp hrule
    specialize hinp ident' mid_i _ hrule'
    rcases hinp with ⟨alm_mid_s, mid_s, hrule_s, hexist, hphi'⟩
    refine ⟨ alm_mid_s, mid_s, ?_, ?_, ‹_› ⟩
    . have : (smod.mapInputPorts f).inputs.getIO (f ident') = smod.inputs.getIO ident' := by
        unfold mapInputPorts PortMap.getIO; dsimp
        rw [AssocList.mapKey_find?]; exact h.injective
      rw [rw_rule_execution this]; convert hrule_s; simp
    · assumption
  · apply href.outputs
  · apply href.internals

theorem refines'_mapInputPorts {I S} {imod : Module Ident I} {smod : Module Ident S} {f}
  (h : Function.Bijective f) :
  imod ⊑' smod →
  imod.mapInputPorts f ⊑' smod.mapInputPorts f := by
  intro href; rcases href with ⟨_, R, href, hind⟩
  refine ⟨MatchInterface_mapInputPorts (imod := imod) (smod := smod) h, R, ?_, ?_⟩
  · solve_by_elim [refines_φ_mapInputPorts]
  · intro _ _ HR; specialize hind _ _ HR
    solve_by_elim [indistinguishable_mapInputPorts]

theorem refines_mapInputPorts {I S} {imod : Module Ident I} {smod : Module Ident S} {f} (h : Function.Bijective f) :
  imod ⊑ smod →
  imod.mapInputPorts f ⊑ smod.mapInputPorts f := by
  simp [←refines'_refines_iff]; solve_by_elim [refines'_mapInputPorts]

theorem refines_φ_mapOutputPorts {I S} {imod : Module Ident I} {smod : Module Ident S}
  [MatchInterface imod smod] {f φ} {h : Function.Bijective f} :
  have _ := MatchInterface_mapOutputPorts (imod := imod) (smod := smod) h
  imod ⊑_{φ} smod →
  imod.mapOutputPorts f ⊑_{φ} smod.mapOutputPorts f := by
  intro hinj href
  unfold refines_φ at *
  intro init_i init_s hphi
  specialize href _ _ hphi
  constructor
  · apply href.inputs
  · rcases href with ⟨h1, hinp, h2⟩; clear h1 h2
    intro ident mid_i v hrule
    have := Function.bijective_iff_existsUnique f |>.mp h ident
    rcases this with ⟨ident', mapIdent, uniq⟩
    subst ident
    have : (imod.mapOutputPorts f).outputs.getIO (f ident') = imod.outputs.getIO ident' := by
      unfold mapOutputPorts PortMap.getIO; dsimp
      rw [AssocList.mapKey_find?]; exact h.injective
    have hrule' := (rw_rule_execution this).mp hrule
    specialize hinp ident' mid_i _ hrule'
    rcases hinp with ⟨mid_s, hrule_s, hphi'⟩
    refine ⟨ mid_s, ?_, ‹_› ⟩
    . have : (smod.mapOutputPorts f).outputs.getIO (f ident') = smod.outputs.getIO ident' := by
        unfold mapOutputPorts PortMap.getIO; dsimp
        rw [AssocList.mapKey_find?]; exact h.injective
      rw [rw_rule_execution this]; convert hrule_s; simp
  · apply href.internals

theorem refines'_mapOutputPorts {I S} {imod : Module Ident I} {smod : Module Ident S} {f}
  (h : Function.Bijective f) :
  imod ⊑' smod →
  imod.mapOutputPorts f ⊑' smod.mapOutputPorts f := by
  intro href; rcases href with ⟨_, R, href, hind⟩
  refine ⟨MatchInterface_mapOutputPorts (imod := imod) (smod := smod) h, R, ?_, ?_⟩
  · solve_by_elim [refines_φ_mapOutputPorts]
  · intro _ _ HR; specialize hind _ _ HR
    solve_by_elim [indistinguishable_mapOutputPorts]

theorem refines_mapOutputPorts {I S} {imod : Module Ident I} {smod : Module Ident S} {f} (h : Function.Bijective f) :
  imod ⊑ smod →
  imod.mapOutputPorts f ⊑ smod.mapOutputPorts f := by
  simp [←refines'_refines_iff]; solve_by_elim [refines'_mapOutputPorts]

theorem refines_mapPorts {I S} {imod : Module Ident I} {smod : Module Ident S} {f} (h : Function.Bijective f) :
  imod ⊑ smod →
  imod.mapPorts f ⊑ smod.mapPorts f := by
  intro Href; unfold mapPorts
  solve_by_elim [refines_mapOutputPorts, refines_mapInputPorts]

theorem refines_mapPorts2 {I S} {imod : Module Ident I} {smod : Module Ident S} {f g}
  (h : Function.Bijective f) (h : Function.Bijective g) :
  imod ⊑ smod →
  imod.mapPorts2 f g ⊑ smod.mapPorts2 f g := by
  intro Href; unfold mapPorts2
  solve_by_elim [refines_mapOutputPorts, refines_mapInputPorts]

theorem refines_renamePorts {I S} {imod : Module Ident I} {smod : Module Ident S} {p} :
  imod ⊑ smod →
  imod.renamePorts p ⊑ smod.renamePorts p := by
  intro Href; unfold renamePorts
  solve_by_elim [refines_mapPorts2, bijectivePortRenaming_bijective]

end Refinement

end Module

instance {n} : OfNat (InstIdent Nat) n where
  ofNat := .internal n

instance {n} : OfNat (InternalPort Nat) n where
  ofNat := ⟨ .top, n ⟩

abbrev NatModule := Module Nat

abbrev StringModule := Module String

@[drunfold] def NatModule.stringify {T} (m : NatModule T) : StringModule T :=
  m |>.mapIdent (λ x =>  "in" ++ toString (x + 1)) (λ x => "out" ++ toString (x + 1))

def IdentMap.toInterface {Ident} (i : IdentMap Ident (Σ T, Module Ident T))
  : IdentMap Ident (Interface Ident) :=
  i.mapVal (λ _ x => x.snd |>.toInterface)

abbrev TModule Ident := Σ T, Module Ident T
abbrev TModule1 Ident := Σ T : Type, Module Ident T

end DataflowRewriter
