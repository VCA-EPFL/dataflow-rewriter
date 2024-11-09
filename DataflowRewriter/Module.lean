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
import Mathlib.Tactic.Common

open Batteries (AssocList)

namespace DataflowRewriter

/-- A function `f : α → β` is called injective if `f x = f y` implies `x = y`. -/
def Injective {α β} (f : α → β) : Prop :=
  ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂

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

def connect'' {Ti To S} (ruleO : S → To → S → Prop) (ruleI : S → Ti → S → Prop) : S → S → Prop :=
  (λ st st' =>
        ∀ wf : To = Ti,
          ∃ consumed_output output, ruleO st output consumed_output
            ∧ ruleI consumed_output (wf.mp output) st')

/--
`connect'` will produce a new rule that fuses an input with an output, with a
precondition that the input and output type must match.
-/
@[drunfold] def connect' {S : Type _} (mod : Module Ident S) (o i : InternalPort Ident) : Module Ident S :=
  { inputs := mod.inputs.eraseAll i ,
    outputs :=  mod.outputs.eraseAll o,
    internals := connect'' (mod.outputs.getIO o).2 (mod.inputs.getIO i).2 :: mod.internals }

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

@[drunfold] def mapPorts {S : Type _} (mod : Module Ident S) (f : InternalPort Ident → InternalPort Ident) : Module Ident S :=
  { mod with inputs := mod.inputs.mapKey f,
             outputs := mod.outputs.mapKey f,
  }

@[drunfold] def mapInputPorts {S} (mod : Module Ident S) (f : InternalPort Ident → InternalPort Ident) : Module Ident S :=
  { mod with inputs := mod.inputs.mapKey f }

@[drunfold] def mapOutputPorts {S} (mod : Module Ident S) (f : InternalPort Ident → InternalPort Ident) : Module Ident S :=
  { mod with outputs := mod.outputs.mapKey f }

def renamePorts {S} (m : Module Ident S) (p : PortMapping Ident) : Module Ident S :=
  m.mapInputPorts (λ k => p.input.find? k |>.getD k)
  |>.mapOutputPorts (λ k => p.output.find? k |>.getD k)

theorem find?_inputs_left {S T} {mod1 : Module Ident S} {mod2 : Module Ident T} {ident rule} :
  mod1.inputs.find? ident = some rule →
  (mod1.product mod2).inputs.find? ident = some (liftL rule) := by sorry

theorem disjoint_find?_inputs_right {S T} {mod1 : Module Ident S} {mod2 : Module Ident T} {ident rule} :
  ¬ mod1.inputs.contains ident →
  mod2.inputs.find? ident = some rule →
  (mod1.product mod2).inputs.find? ident = some (liftR rule) := by sorry

theorem find?_outputs_left {S T} {mod1 : Module Ident S} {mod2 : Module Ident T} {ident rule} :
  mod1.outputs.find? ident = some rule →
  (mod1.product mod2).outputs.find? ident = some (liftL rule) := by sorry

theorem find?_outputs_right {S T} {mod1 : Module Ident S} {mod2 : Module Ident T} {ident rule} :
  ¬ mod1.outputs.contains ident →
  mod2.outputs.find? ident = some rule →
  (mod1.product mod2).outputs.find? ident = some (liftR rule) := by sorry

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

theorem renamePorts_empty {m : Module Ident S} :
  m.renamePorts ∅ = m := by
  unfold renamePorts
  have : (fun k => (Batteries.AssocList.find? k (∅ : PortMapping Ident).output).getD k) = id := by rfl
  have : (fun k => (Batteries.AssocList.find? k (∅ : PortMapping Ident).input).getD k) = id := by rfl
  simp only [*, mapInputPorts_id, mapOutputPorts_id]

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

theorem MatchInterface_Disjoint {I J S K} {imod : Module Ident I} {smod : Module Ident S} {imod' : Module Ident J} {smod' : Module Ident K}
  [MatchInterface imod smod]
  [MatchInterface imod' smod'] :
  Disjoint imod imod' →
  Disjoint smod smod' := by sorry

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

end Match

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
    imod.inputs.contains ident →
    (imod.inputs.getIO ident).2 init_i v new_i →
    ∃ new_s, (smod.inputs.getIO ident).2 init_s ((mm.input_types ident).mp v) new_s
  outputs_indistinguishable : ∀ ident new_i v,
    imod.outputs.contains ident →
    (imod.outputs.getIO ident).2 init_i v new_i →
    ∃ new_s, (smod.outputs.getIO ident).2 init_s ((mm.output_types ident).mp v) new_s

structure comp_refines (R : I → S → Prop) (init_i : I) (init_s : S) : Prop where
  inputs :
    ∀ ident mid_i v,
      imod.inputs.contains ident →
      (imod.inputs.getIO ident).2 init_i v mid_i →
      ∃ almost_mid_s mid_s,
        (smod.inputs.getIO ident).2 init_s ((mm.input_types ident).mp v) almost_mid_s
        ∧ existSR smod.internals almost_mid_s mid_s
        ∧ R mid_i mid_s
  outputs :
    ∀ ident mid_i v,
      imod.outputs.contains ident →
      (imod.outputs.getIO ident).2 init_i v mid_i →
      ∃ almost_mid_s mid_s,
        (smod.outputs.getIO ident).2 init_s ((mm.output_types ident).mp v) almost_mid_s
        ∧ existSR smod.internals almost_mid_s mid_s
        ∧ R mid_i mid_s
  internals :
    ∀ rule mid_i,
      rule ∈ imod.internals →
      rule init_i mid_i →
      ∃ mid_s,
        existSR smod.internals init_s mid_s
        ∧ R mid_i mid_s

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

def refines_φ (R : I → S → Prop) :=
  ∀ (init_i : I) (init_s : S),
    R init_i init_s →
     comp_refines imod smod R init_i init_s

notation:35 x " ⊑_{" R:35 "} " y:34 => refines_φ x y R

theorem refines_φ_reflexive : imod ⊑_{Eq} imod := by
  intro init_i init_s heq; subst_vars
  constructor
  · intro ident mid_i v hcont hrule
    refine ⟨ mid_i, mid_i, hrule, existSR.done _, rfl ⟩
  · intro ident mid_i v hcont hrule
    refine ⟨ mid_i, mid_i, hrule, existSR.done _, rfl ⟩
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
    intro ident mid_i v Hcont Hrule
    specialize h1inp _ _ _ Hcont Hrule
    rcases h1inp with ⟨ mid_mid_j, mid_j, hrule₁, hexists₁, hphi₁ ⟩
    specialize h2inp _ _ _ sorry hrule₁
    rcases h2inp with ⟨ mid_mid_s, mid_s, hrule₂, hexists₂, hphi₂ ⟩
    rcases refines_φ_multistep _ _ _ h2 _ _ hphi₂ _ hexists₁ with ⟨ mid_s₃, hexists₃, hphi₃ ⟩
    refine ⟨ ?_, mid_s₃, ?inp.and1, ?inp.and2, mid_j, ?_, ?_ ⟩
    case and1 => convert hrule₂; simp
    case and2 => solve_by_elim [existSR_transitive]
    all_goals assumption
  · clear h1inp h1int h2inp h2int
    intro ident mid_i v Hcont Hrule
    specialize h1out _ _ _ Hcont Hrule
    rcases h1out with ⟨ mid_mid_j, mid_j, hrule₁, hexists₁, hphi₁ ⟩
    specialize h2out _ _ _ sorry hrule₁
    rcases h2out with ⟨ mid_mid_s, mid_s, hrule₂, hexists₂, hphi₂ ⟩
    rcases refines_φ_multistep _ _ _ h2 _ _ hphi₂ _ hexists₁ with ⟨ mid_s₃, hexists₃, hphi₃ ⟩
    refine ⟨ ?_, mid_s₃, ?out.and1, ?out.and2, mid_j, ?_, ?_ ⟩
    case and1 => convert hrule₂; simp
    case and2 => solve_by_elim [existSR_transitive]
    all_goals assumption
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
  · intro ident mid_i v Hcont Hrule
    specialize Hin ident mid_i v Hcont Hrule
    tauto
  · intro ident mid_i v Hcont Hrule
    specialize Hout ident mid_i v Hcont Hrule
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
  · simp (config := {contextual := true})

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

theorem indistinguishability_product_left {J K} {i i₂ s s₂} {imod₂ : Module Ident J} {smod₂ : Module Ident K}
  [MatchInterface imod smod]
  [MatchInterface imod₂ smod₂]
  [Nonempty J] :
  Disjoint imod imod₂ →
  (imod.product imod₂).indistinguishable (smod.product smod₂) (i, i₂) (s, s₂) →
  imod.indistinguishable smod i s := by
  intro hdisj hindist
  have hdisj' : Disjoint smod smod₂ := MatchInterface_Disjoint hdisj
  rcases hindist with ⟨hindist_input, hindist_output⟩
  constructor
  intro ident new_i v hcontains hrule
  rcases ‹Nonempty J› with ⟨new_j⟩
  specialize hindist_input ident (new_i, new_j)
  all_goals sorry

theorem indistinguishability_product_right {J K} {i i₂ s s₂} {imod₂ : Module Ident J} {smod₂ : Module Ident K}
  [MatchInterface imod smod]
  [MatchInterface imod₂ smod₂]
  [Nonempty I] :
  Disjoint imod imod₂ →
  (imod.product imod₂).indistinguishable (smod.product smod₂) (i, i₂) (s, s₂) →
  imod₂.indistinguishable smod₂ i₂ s₂ := by
  intro hdisj hindist
  rcases hindist with ⟨hindist_input, hindist_output⟩
  constructor
  intro ident new_j v hcontains hrule
  rcases ‹Nonempty I› with ⟨new_i⟩
  specialize hindist_input ident (new_i, new_j)
  all_goals sorry

theorem indistinguishability_product {J K} {i i₂ s s₂} {imod₂ : Module Ident J} {smod₂ : Module Ident K}
  [MatchInterface imod smod]
  [MatchInterface imod₂ smod₂] :
  imod.indistinguishable smod i s →
  imod₂.indistinguishable smod₂ i₂ s₂ →
  (imod.product imod₂).indistinguishable (smod.product smod₂) (i, i₂) (s, s₂) := by sorry

@[reducible] def cast_first {β : Type _ → Type _} {a b : (Σ α, β α)} (h : a = b) : a.fst = b.fst := by
  subst_vars; rfl

theorem rw_rule_execution {S : Type _} {a b : Σ (T : Type _), S → T → S → Prop} {s s'} {v : a.fst} (h : a = b) :
  a.snd s v s' ↔ b.snd s ((cast_first h).mp v) s' := by subst_vars; rfl

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

theorem refines_φ_product {J K} [Nonempty J] [Nonempty I] {imod₂ : Module Ident J} {smod₂ : Module Ident K}
  [MatchInterface imod smod]
  [MatchInterface imod₂ smod₂] {φ₁ φ₂} :
    imod ⊑_{φ₁} smod →
    imod₂ ⊑_{φ₂} smod₂ →
    imod.product imod₂ ⊑_{λ a b => φ₁ a.1 b.1 ∧ φ₂ a.2 b.2} smod.product smod₂ := by stop
  intro href₁ href₂
  have mm_prod : MatchInterface (imod.product imod₂) (smod.product smod₂) := by apply MatchInterface_product
  unfold refines_φ at *
  intro ⟨init_i, init_i₂⟩ ⟨init_s,init_s₂⟩ hφ
  specialize href₁ init_i init_s hφ.left
  specialize href₂ init_i₂ init_s₂ hφ.right
  constructor
  · intro ident ⟨mid_i, mid_i₂⟩ hgetio hcontains hrule
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
      specialize href_in ident mid_i (cast2.mp hgetio) hcontains₂ hrule₂
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
      specialize href_in ident mid_i₂ (cast2.mp hgetio) hcontains₂ hrule₂
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
        have : (AssocList.mapVal (fun x => liftR) smod₂.inputs).find? ident = some (@liftR S _ Srule) := by
          rw [←AssocList.find?_map_comm]; rw [HSrule]; rfl
        have s : (smod.product smod₂).inputs.getIO ident = liftR (smod₂.inputs.getIO ident) := by
          skip; dsimp [Module.product, PortMap.getIO];
          rw [AssocList.append_find_right, this]
          · rw [HSrule]; rfl
          · rw [hruleIn'none]
        rw [rw_rule_execution s]
        dsimp [liftL]; refine ⟨?_, rfl⟩; convert hrule₃; simp
      · solve_by_elim [existSR_append_right, existSR_liftR']
      · apply hφ.left
      · assumption
  · intro ident ⟨mid_i, mid_i₂⟩ hgetio hcontains hrule
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
      specialize href_out ident mid_i (cast2.mp hgetio) hcontains₂ hrule₂
      rcases href_out with ⟨almost_mid_s, mid_s, hrule₃, hexists, hφ₃⟩
      refine ⟨ (almost_mid_s, ‹_›), (mid_s, ‹_›), ?_, ?_, ?_, ?_ ⟩
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
      · solve_by_elim [existSR_append_left, existSR_liftL']
      · assumption
      · apply hφ.right
    case inr =>
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
      specialize href_out ident mid_i₂ (cast2.mp hgetio) hcontains₂ hrule₂
      rcases href_out with ⟨almost_mid_s, mid_s, hrule₃, hexists, hφ₃⟩
      refine ⟨ (‹_›, almost_mid_s), (‹_›, mid_s), ?_, ?_, ?_, ?_ ⟩
      · have : ∃ y, smod₂.outputs.find? ident = some y := by
          have := ‹MatchInterface imod₂ smod₂›.outputs_present ident
          rw [h] at this
          simp [-AssocList.find?_eq] at this
          exact Option.isSome_iff_exists.mp this
        rcases this with ⟨Srule, HSrule⟩
        have : (AssocList.mapVal (fun x => liftR) smod₂.outputs).find? ident = some (@liftR S _ Srule) := by
          rw [←AssocList.find?_map_comm]; rw [HSrule]; rfl
        have s : (smod.product smod₂).outputs.getIO ident = liftR (smod₂.outputs.getIO ident) := by
          have : Disjoint smod smod₂ := MatchInterface_Disjoint hdisj
          rcases this with ⟨l,r⟩
          skip; dsimp [Module.product, PortMap.getIO];
          rw [AssocList.append_find_right_disjoint (a := (AssocList.mapVal (fun x => liftL) smod.outputs)) (AssocList.disjoint_keys_mapVal_both r) this]
          rw [HSrule]; rfl
        rw [rw_rule_execution s]
        dsimp [liftL]; refine ⟨?_, rfl⟩; convert hrule₃; simp
      · solve_by_elim [existSR_append_right, existSR_liftR']
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

theorem refines_product {J K} [Nonempty J] [Nonempty I] (imod₂ : Module Ident J) (smod₂ : Module Ident K):
    Disjoint imod imod₂ →
    -- imod.disjoint smod →
    imod ⊑ smod →
    imod₂ ⊑ smod₂ →
    imod.product imod₂ ⊑ smod.product smod₂ := by
  -- intro hdisj
  intro hdisj href₁ href₂
  rcases href₁ with ⟨_, R, ref⟩
  rcases href₂ with ⟨_, R2, ref₂⟩
  have hdisj₂ := MatchInterface_Disjoint (smod' := smod₂) (smod := smod) ‹_›
  refine ⟨ inferInstance, (λ a b => R a.1 b.1 ∧ R2 a.2 b.2), ?_ ⟩
  unfold refines_φ at *
  intro ⟨init_i, init_i₂⟩ ⟨init_s,init_s₂⟩ hφ
  specialize ref init_i init_s
  specialize ref₂ init_i₂ init_s₂
  have hφ₁ : (fun x y => imod.indistinguishable smod x y ∧ R x y) init_i init_s :=
    ⟨indistinguishability_product_left hdisj hφ.left, hφ.right.left⟩
  have hφ₂ : (fun x y => imod₂.indistinguishable smod₂ x y ∧ R2 x y) init_i₂ init_s₂ :=
    ⟨indistinguishability_product_right hdisj hφ.left, hφ.right.right⟩
  specialize ref hφ₁
  specialize ref₂ hφ₂
  all_goals sorry

theorem refines'_connect {o i} :
    imod ⊑' smod →
    imod.connect' o i ⊑' smod.connect' o i := by
  intro href₁
  rcases href₁ with ⟨_, R, ref, ind⟩
  unfold refines' refines_φ at *
  refine ⟨inferInstance, R, ?_, ?_⟩
  · intro init_i init_s hphi
    sorry
  · intro x y hphi; specialize ind _ _ hphi
    sorry

theorem refines_connect {o i} :
    imod ⊑ smod →
    imod.connect' o i ⊑ smod.connect' o i := by
  intro href₁
  rcases href₁ with ⟨_, R, ref⟩
  unfold refines refines_φ at *
  refine ⟨inferInstance, (fun x y => (R x y) ∧ (imod.indistinguishable smod x y)), ?_⟩
  intro init_i init_s ⟨hindist, hφ⟩
  rcases hφ with ⟨ hl, hr ⟩
  have : (fun x y => imod.indistinguishable smod x y ∧ R x y) init_i init_s := by
    and_intros <;> assumption
  specialize ref _ _ this
  all_goals sorry

theorem refines_renamePorts {I S} {imod : Module Ident I} {smod : Module Ident S} {f}:
  imod ⊑ smod →
  imod.renamePorts f ⊑ smod.renamePorts f := by sorry

end Refinement

end Module

instance {n} : OfNat (InstIdent Nat) n where
  ofNat := .internal n

instance {n} : OfNat (InternalPort Nat) n where
  ofNat := ⟨ .top, n ⟩

abbrev NatModule := Module Nat

abbrev StringModule := Module String

@[drunfold] def NatModule.stringify {T} (m : NatModule T) : StringModule T :=
  m |>.mapIdent (λ x =>  "inp" ++ toString x) (λ x => "out" ++ toString x)

def IdentMap.toInterface {Ident} (i : IdentMap Ident (Σ T, Module Ident T))
  : IdentMap Ident (Interface Ident) :=
  i.mapVal (λ _ x => x.snd |>.toInterface)

abbrev TModule Ident := Σ T, Module Ident T

end DataflowRewriter
