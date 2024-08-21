import Leanses
import Lean
import Init.Data.BitVec.Lemmas
import Mathlib
import DataflowRewriter.Simp
import Qq

open Qq

open Batteries (AssocList)
open Batteries (RBMap)

open Lean.Meta Lean.Elab

namespace DataflowRewriter

abbrev Ident := String
deriving instance BEq for Ident

deriving instance Repr for Ident
deriving instance Hashable for Ident
deriving instance DecidableEq for Ident
deriving instance Ord for Ident

deriving instance Repr for AssocList

abbrev IdentMap α := AssocList Ident α

inductive ExprLow where
  | base : Ident → Ident → ExprLow
  | product : ExprLow → ExprLow → ExprLow
  | connect : ExprLow → Nat → Nat → ExprLow
  deriving Repr

structure Module (S : Type u₁) : Type (max u₁ 1) where
  inputs : List ((T : Type 0) × (S -> T -> S -> Prop))
  outputs : List ((T : Type 0) × (S -> T -> S -> Prop))
  internals : List (S -> S -> Prop)

mklenses Module
open Module.l

def empty : Module S := {inputs := [], outputs := [], internals:= []}

@[simp]
def _root_.List.remove {α : Type u} (as : List α) (i : Fin as.length) : List α := as.eraseIdx i

def connect (mod : Module S) (i : Fin mod.inputs.length) (o : Fin mod.outputs.length)
      (wf : (mod.inputs.get i).1 = (mod.outputs.get o).1) : Module S :=
       { inputs := mod.inputs.remove i,
         outputs :=  mod.outputs.remove o,
         internals :=  (λ st st' => ∃ consumed_output output, (mod.outputs.get o).2 st output consumed_output ∧
                              (mod.inputs.get i).2 consumed_output (Eq.rec id wf output) st')
                        :: mod.internals }

-- @[simp]
-- def source (l : List ((T : Type) × T)) : Module (Fin l.length → ((T : Type) × List T)) :=
--   { inputs := ((List.drange l.length).zip l).map
--               (λ (n, (Sigma.mk T d)) => ⟨ T, λ s t s' => s' = update_Fin n ⟩),
--     internals := [],
--     outputs := l.map (λ (Sigma.mk T d) => ⟨ T, λ _ t _ => t = d ⟩)
--   }

@[simp]
def io (T : Type) : Module (List T) :=
  { inputs := [⟨ T, λ s t s' => s' = t :: s ⟩],
    internals := [],
    outputs := [⟨ T, λ s t s' => s = s' ++ [t] ⟩]
  }

@[simp]
def sink (l : List Type) : Module Unit :=
  { inputs := l.map (λ T => ⟨ T, λ _ _ _ => True ⟩),
    internals := [],
    outputs := []
  }

@[simp]
def connect' (mod : Module S) (i : Fin mod.inputs.length) (o : Fin mod.outputs.length) : Module S :=
       { inputs := mod.inputs.remove i ,
         outputs :=  mod.outputs.remove o,
         internals :=  (λ st st' => ∀ wf : (mod.inputs.get i).1 = (mod.outputs.get o).1,
                            ∃ consumed_output output, (mod.outputs.get o).2 st output consumed_output ∧
                              (mod.inputs.get i).2 consumed_output (Eq.rec id wf output) st')
                              :: mod.internals }

@[simp]
def liftL (x: (T : Type _) × (S -> T -> S -> Prop)) : (T : Type _) × (S × S' -> T -> S × S' -> Prop) :=
      ⟨ x.1, λ (a,b) ret (a',b') => x.2 a ret a' ∧ b = b' ⟩

@[simp]
def liftR (x: (T : Type _) × (S' -> T -> S' -> Prop)) : (T : Type _) × (S × S' -> T -> S × S' -> Prop) :=
      ⟨ x.1, λ (a,b) ret (a',b') => x.2 b ret b' ∧ a = a' ⟩

@[simp]
def liftL' (x:  S -> S -> Prop) : S × S' -> S × S' -> Prop :=
      λ (a,b) (a',b') => x a a' ∧ b = b'

@[simp]
def liftR' (x:  S' -> S' -> Prop) : S × S' -> S × S' -> Prop :=
      λ (a,b) (a',b') => x b b' ∧ a = a'

@[simp]
def product (mod1 : Module S) (mod2: Module S') : Module (S × S') :=
      { inputs := mod1.inputs.map liftL ++ mod2.inputs.map liftR,
        outputs := mod1.outputs.map liftL ++ mod2.outputs.map liftR,
        internals := mod1.internals.map liftL' ++ mod2.internals.map liftR'
      }
@[simp]
def merge_inputs (mod : Module S) (in1 in2 : Fin (List.length mod.inputs)) : Module S  :=
      { inputs :=
        let in1_t := mod.inputs.get in1;
        let in2_t := mod.inputs.get in2;
        let rmin2 := List.remove mod.inputs in2;
        List.set rmin2 in2.1 ⟨ in1_t.1 × in2_t.1, λ s (v1,v2) s' =>
              ∃ s_int, in1_t.2 s v1 s_int ∧
              in2_t.2 s_int v2 s'⟩
      ,
        outputs := mod.outputs,
        internals := mod.internals }
@[simp]
def merge_outputs (mod : Module S) (out1 out2 : Fin (List.length mod.outputs)) : Module S  :=
      { outputs :=
        let out1_t := mod.outputs.get out1;
        let out2_t := mod.outputs.get out2;
        let rmout2 := List.remove mod.outputs out2;
        List.set rmout2 out2.1 ⟨ out1_t.1 × out2_t.1, λ s (v1,v2) s' =>
              ∃ s_int, out1_t.2 s v1 s_int ∧
              out2_t.2 s_int v2 s'⟩
      ,
        inputs := mod.inputs,
        internals := mod.internals }

@[simp]
def merge T : Module (List T):=
      { inputs := [⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩,
                   ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩],
        outputs := [⟨ T, λ oldList oldElement newList => ∃ i, newList = oldList.remove i ∧ oldElement = oldList.get i ⟩],
        internals := []
      }

@[simp]
def fork T : Module (List T):=
      { inputs := [⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩],
        outputs := [ ⟨ T, λ oldList oldElement newList => ∃ i, newList = oldList.remove i ∧ oldElement = oldList.get i ⟩
                   , ⟨ T, λ oldList oldElement newList => ∃ i, newList = oldList.remove i ∧ oldElement = oldList.get i ⟩
                   ],
        internals := []
      }

def composed_threemerge T :=
  let merge1 := merge T;
  let merge2 := merge T;
  let prod := product merge1 merge2;
  connect prod (by { refine ⟨2, ?_⟩; simp (config := { zetaDelta := true}) at * } )
               (by { refine ⟨0, ?_⟩; simp (config := { zetaDelta := true}) at * } )
               (by { simp (config := { zetaDelta := true}) at *})

def threemerge T : Module (List T):=
  { inputs := [⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩,
               ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩,
               ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩],
    outputs := [⟨ T, λ oldList oldElement newList => ∃ i, newList = oldList.remove i ∧ oldElement = oldList.get i ⟩],
    internals := []
  }

@[simp]
def getIO.{u₁, u₂} {S : Type u₁} (l: List ((T : Type u₂) × (S -> T -> S -> Prop))) (n : Nat): ((T : Type u₂) × (S -> T -> S -> Prop)) :=
  l.getD n (⟨ PUnit, λ _ _ _ => True ⟩)

@[simp]
def getRule {S : Type _} (l : List (S → S → Prop)) (n : Nat) : (S → S → Prop) :=
  l.getD n (λ _ _ => True)

variable (baseModules : Fin n → ((T : Type) × Module T))

structure matching_interface (imod : Module I) (smod : Module S) : Prop where
  input_types : ∀ (ident : Fin imod.inputs.length), (imod.inputs.get ident).1 = (getIO smod.inputs ident).1
  output_types : ∀ (ident : Fin imod.outputs.length), (imod.outputs.get ident).1 = (getIO smod.outputs ident).1

section Trace

variable {S : Type _}
variable (mod : Module S)

inductive existSR : S → S → Prop where
  | done : ∀ init, existSR init init
  | step :
    ∀ init mid final n,
      (getRule mod.internals n) init mid →
      existSR mid final →
      existSR init final

end Trace

section Refinement

variable {I : Type _}
variable {S : Type _}
variable (imod : Module I)
variable (smod : Module S)

variable (matching : matching_interface imod smod)

/--
This could be made even more flexible by passing a custom type comparison
function for the inputs and outputs.  For now this might be general enough
though.
-/
structure indistinguishable (init_i : I) (init_s : S) : Prop where
  inputs_indistinguishable : ∀ (ident : Fin imod.inputs.length)
  new_i v,
    (imod.inputs.get ident).2 init_i v new_i →
    ∃ new_s, (getIO smod.inputs ident).2 init_s ((matching.input_types ident).mp v) new_s
  outputs_indistinguishable : ∀ ident new_i v,
    (imod.outputs.get ident).2 init_i v new_i →
    ∃ new_s, (getIO smod.outputs ident).2 init_s ((matching.output_types ident).mp v) new_s

structure comp_refines (R : I → S → Prop) (init_i : I) (init_s : S) : Prop where
  inputs :
    ∀ (ident : Fin imod.inputs.length) mid_i v,
      (imod.inputs.get ident).2 init_i v mid_i →
      ∃ almost_mid_s mid_s,
        (getIO smod.inputs ident).2 init_s ((matching.input_types ident).mp v) almost_mid_s
        ∧ existSR smod almost_mid_s mid_s
        ∧ R mid_i mid_s
        ∧ indistinguishable imod smod matching mid_i mid_s
  outputs :
    ∀ (ident : Fin imod.outputs.length) mid_i v,
      (imod.outputs.get ident).2 init_i v mid_i →
      ∃ almost_mid_s mid_s,
        (getIO smod.outputs ident).2 init_s ((matching.output_types ident).mp v) almost_mid_s
        ∧ existSR smod almost_mid_s mid_s
        ∧ R mid_i mid_s
        ∧ indistinguishable imod smod matching mid_i mid_s
  internals :
    ∀ (ident : Fin imod.internals.length) mid_i,
      (getRule imod.internals ident) init_i mid_i →
      ∃ mid_s,
        existSR smod init_s mid_s
        ∧ R mid_i mid_s
        ∧ indistinguishable imod smod matching mid_i mid_s

def refines (R : I → S → Prop) :=
  ∀ (init_i : I) (init_s : S),
    R init_i init_s →
    indistinguishable imod smod matching init_i init_s →
    comp_refines imod smod matching R init_i init_s

end Refinement

section Semantics

@[simp]
def build_module' (e : ExprLow) (ε : IdentMap ((T: Type _) × Module T))
  : Option ((T: Type _) × Module T) :=
  match e with
  | .base _ e => ε.find? e
  | .connect e' i o => do
    let e ← build_module' e' ε
    if hi : i < e.2.inputs.length then
      if ho : o < e.2.outputs.length then
        let i := ⟨i, hi⟩;
        let o := ⟨o, ho⟩;
        return ⟨e.1, connect' e.2 i o⟩
    .none
  | .product a b => do
    let a <- build_module' a ε;
    let b <- build_module' b ε;
    return ⟨a.1 × b.1, product a.2 b.2⟩

end Semantics

section RefinementTheorem

end RefinementTheorem

end DataflowRewriter
