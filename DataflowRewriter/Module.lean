import Leanses
import Lean
import Init.Data.BitVec.Lemmas
import Mathlib.Tactic.FinCases

open Lean Meta Elab
namespace DataflowRewriter

structure Module (S : Type u₁) : Type (max u₁ (u₂ + 1)) where
  inputs : List ((T : Type u₂) × (S -> T -> S -> Prop))
  outputs : List ((T : Type u₂) × (S -> T -> S -> Prop))
  internals : List (S -> S -> Prop)

mklenses Module
open Module.l


def empty : Module S := {inputs := [], outputs := [], internals:= []}

@[simp]
def List.remove {α : Type u} : (as : List α) → Fin as.length → List α
  | List.cons _ as,  ⟨0, _⟩ => as
  | List.cons a as, ⟨Nat.succ i, h⟩ => a::remove as ⟨i, Nat.le_of_succ_le_succ h⟩


def connect (mod : Module S) (i : Fin (List.length mod.inputs)) (o : Fin (List.length mod.outputs))
      (wf : (List.get mod.inputs i).1 = (List.get mod.outputs o).1) : Module S :=
       { inputs := List.remove mod.inputs i ,
         outputs :=  List.remove mod.outputs o,
         internals :=  (fun st st' => ∃ consumed_output output, (List.get mod.outputs o).2 st output consumed_output /\
                              (List.get mod.inputs i).2 consumed_output (Eq.rec id wf output) st')
                        :: mod.internals }

@[simp]
def connect' (mod : Module S) (i : Fin (List.length mod.inputs)) (o : Fin (List.length mod.outputs)) : Module S :=
       { inputs := List.remove mod.inputs i ,
         outputs :=  List.remove mod.outputs o,
         internals :=  (fun st st' => ∀ wf : (List.get mod.inputs i).1 = (List.get mod.outputs o).1,
                            ∃ consumed_output output, (List.get mod.outputs o).2 st output consumed_output /\
                              (List.get mod.inputs i).2 consumed_output (Eq.rec id wf output) st')
                              :: mod.internals }

@[simp]
def liftL (x: (T : Type _) × (S -> T -> S -> Prop)) : (T : Type _) × (S × S' -> T -> S × S' -> Prop) :=
      ⟨ x.1, fun (a,b) ret (a',b') => x.2 a ret a' /\ b = b' ⟩

@[simp]
def liftR (x: (T : Type _) × (S' -> T -> S' -> Prop)) : (T : Type _) × (S × S' -> T -> S × S' -> Prop) :=
      ⟨ x.1, fun (a,b) ret (a',b') => x.2 b ret b' /\ a = a' ⟩

@[simp]
def liftL' (x:  S -> S -> Prop) : S × S' -> S × S' -> Prop :=
      fun (a,b) (a',b') => x a a' /\ b = b'

@[simp]
def liftR' (x:  S' -> S' -> Prop) : S × S' -> S × S' -> Prop :=
      fun (a,b) (a',b') => x b b' /\ a = a'

@[simp]
def product (mod1 : Module S) (mod2: Module S') : Module (S × S') :=
      { inputs := List.map liftL mod1.inputs ++ List.map liftR mod2.inputs,
        outputs := List.map liftL mod1.outputs ++ List.map liftR mod2.outputs,
        internals := List.map liftL' mod1.internals ++ List.map liftR' mod2.internals
      }

@[simp]
def merge T : Module (List T):=
      { inputs := [⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩,
                   ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩],
        outputs := [⟨ T, λ oldList oldElement newList => oldList = newList ++ [oldElement] ⟩],
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
    outputs := [⟨ T, λ oldList oldElement newList => oldList = newList ++ [oldElement] ⟩],
    internals := []
  }

inductive ExprLow where
  | base : Nat -> ExprLow
  | product : ExprLow -> ExprLow -> ExprLow
  | connect : ExprLow -> Nat -> Nat -> ExprLow

structure Connection where
  inputInstance  : Nat
  outputInstance : Nat
  inputPort      : Nat
  outputPort     : Nat

structure ExprHigh where
  modules     : List Nat
  connections : List Connection

def lower (e : ExprHigh) : Option ExprLow := by sorry
def higher (e : ExprLow) : Option ExprHigh := by sorry

@[simp]
def getIO.{u₁, u₂} {S : Type u₁} (l: List ((T : Type u₂) × (S -> T -> S -> Prop))) (n : Nat): ((T : Type u₂) × (S -> T -> S -> Prop)) :=
  List.getD l n (⟨ PUnit, fun _ _ _ => True ⟩)

@[simp]
def getRule {S : Type _} (l : List (S → S → Prop)) (n : Nat) : (S → S → Prop) :=
  List.getD l n (fun _ _ => True)

variable (baseModules : Fin n → ((T : Type) × Module T))

structure indistinguishable_strict (imod : Module I) (smod : Module S) : Prop where
  inputs_length : List.length imod.inputs = List.length smod.inputs
  inputs_types : ∀ ident, (List.get imod.inputs ident).1 = (List.get smod.inputs (Eq.rec id inputs_length ident)).1

  inputs_indistinguishable : ∀ ident init_i new_i init_s v,
    (List.get imod.inputs ident).2 init_i v new_i →
    ∃ new_s,
      (List.get smod.inputs (Eq.rec id inputs_length ident)).2 init_s ((inputs_types ident).mp v) new_s

  outputs_length : List.length imod.outputs = List.length smod.outputs
  outputs_types : ∀ ident, (List.get imod.outputs ident).1 = (List.get smod.outputs (Eq.rec id outputs_length ident)).1

  outputs_indistinguishable : ∀ ident init_i new_i init_s v,
    (List.get imod.outputs ident).2 init_i v new_i →
    ∃ new_s,
      (List.get smod.outputs (Eq.rec id outputs_length ident)).2 init_s ((outputs_types ident).mp v) new_s

structure matching_interface (imod : Module I) (smod : Module S) : Prop where
  input_types : ∀ (ident : Fin (List.length imod.inputs)), (List.get imod.inputs ident).1 = (getIO smod.inputs ident).1
  output_types : ∀ (ident : Fin (List.length imod.outputs)), (List.get imod.outputs ident).1 = (getIO smod.outputs ident).1

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
  inputs_indistinguishable : ∀ (ident : Fin (List.length imod.inputs))
  new_i v,
    (List.get imod.inputs ident).2 init_i v new_i →
    ∃ new_s, (getIO smod.inputs ident).2 init_s ((matching.input_types ident).mp v) new_s
  outputs_indistinguishable : ∀ ident new_i v,
    (List.get imod.outputs ident).2 init_i v new_i →
    ∃ new_s, (getIO smod.outputs ident).2 init_s ((matching.output_types ident).mp v) new_s

structure comp_refines (R : I → S → Prop) (init_i : I) (init_s : S) : Prop where
  inputs :
    ∀ (ident : Fin (List.length imod.inputs)) mid_i v,
      (List.get imod.inputs ident).2 init_i v mid_i →
      ∃ almost_mid_s mid_s,
        (getIO smod.inputs ident).2 init_s ((matching.input_types ident).mp v) almost_mid_s
        ∧ existSR smod almost_mid_s mid_s
        ∧ R mid_i mid_s
        ∧ indistinguishable imod smod matching mid_i mid_s
  outputs :
    ∀ (ident : Fin (List.length imod.outputs)) mid_i v,
      (List.get imod.outputs ident).2 init_i v mid_i →
      ∃ almost_mid_s mid_s,
        (getIO smod.outputs ident).2 init_s ((matching.output_types ident).mp v) almost_mid_s
        ∧ existSR smod almost_mid_s mid_s
        ∧ R mid_i mid_s
        ∧ indistinguishable imod smod matching mid_i mid_s
  internals :
    ∀ n mid_i,
      (getRule imod.internals n) init_i mid_i →
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
-- def connect (mod : Module S) (i : Fin (List.length mod.inputs)) (o : Fin (List.length mod.outputs))
--       (wf : (List.get mod.inputs i).1 = (List.get mod.outputs o).1) : Module S :=
--        { inputs := List.remove mod.inputs i ,
--          outputs :=  List.remove mod.outputs o,
--          internals :=  (fun st st' => ∃ consumed_output output, (List.get mod.outputs o).2 st output consumed_output /\
--                               (List.get mod.inputs i).2 consumed_output (Eq.rec id wf output) st')
--                         :: mod.internals }

-- @[simp]
-- def product (mod1 : Module S) (mod2: Module S') : Module (S × S') :=
--       { inputs := List.map liftL mod1.inputs ++ List.map liftR mod2.inputs,
--         outputs := List.map liftL mod1.outputs ++ List.map liftR mod2.outputs,
--         internals := List.map liftL' mod1.internals ++ List.map liftR' mod2.internals
--       }
  -- def wf (e :ExprLow) (build_module: ExprLow -> List ((T: Type _) × Module T) -> Option ((T: Type _) ×  Module T)) (ε : List ((T: Type _) × Module T)): Prop :=
  --   match e with
  --   | ExprLow.base i => True
  --   | ExprLow.connect e' i o =>
  --     let e := build_module e' ε;
  --     match e with
  --     | some e =>
  --     if hi:i<List.length e.2.inputs then
  --       if ho:o<List.length e.2.outputs then
  --         let i := ⟨i, hi⟩;
  --         let o := ⟨o, ho⟩;
  --         ((e.2.inputs.get i).fst = (e.2.outputs.get o).fst) /\ wf e' build_module ε
  --       else True
  --     else True
  --     | none => True
  --   | ExprLow.product a b => True

@[simp]
def build_module' (e : ExprLow) (ε : List ((T: Type _) × Module T))
  : Option ((T: Type _) × Module T) :=
  match e with
  | .base e => ε.get? e
  | .connect e' i o => do
    let e ← build_module' e' ε
    if hi : i < e.2.inputs.length then
      if ho : o < e.2.outputs.length then
        let i := ⟨i, hi⟩;
        let o := ⟨o, ho⟩;
        return ⟨e.1, connect' e.2 i o⟩
      else none
    else none
  | .product a b => do
    let a <- build_module' a ε;
    let b <- build_module' b ε;
    return ⟨a.1 × b.1, product a.2 b.2⟩




-- def build_module (e : ExprLow) (ε : List ((T: Type _) × Module T))
--   : Option ((T: Type _) × Module T) :=
--   match e with
--   | .base e => ε.get? e
--   | .connect e' i o => do
--     let e ← build_module' e' ε
--     if hi : i < e.2.inputs.length then
--       if ho : o < e.2.outputs.length then
--         let i := ⟨i, hi⟩;
--         let o := ⟨o, ho⟩;
--         return ⟨e.1, connect e.2 i o _⟩
--       else none
--     else none
--   | .product a b => do
--     let a <- build_module' a ε;
--     let b <- build_module' b ε;
--     return ⟨a.1 × b.1, product a.2 b.2⟩

end Semantics

section Syntax

end Syntax


@[simp]
def mergeLow : ExprLow :=
  let merge1 := ExprLow.base 0;
  let merge2 := ExprLow.base 0;
  let prod := ExprLow.product merge1 merge2;
  ExprLow.connect prod 2 0

@[simp]
def merge_sem (T: Type _) :=
  match build_module' mergeLow [⟨List T, merge T⟩] with
  | some x => x
  | none => ⟨Unit, empty⟩
#reduce merge_sem Nat
-- #eval (merge_sem Nat).2

theorem lol T :  matching_interface (merge_sem T).snd (threemerge T) :=  by sorry
#print refines
#print indistinguishable
-- set_option pp.proofs true
-- set_option trace.Meta.Tactic.simp.rewrite true
theorem correct_threeway {T: Type _} :
    refines ((merge_sem T).snd) (threemerge T) (lol T)
          (fun x y => by
              simp at x;
              exact (x.1 ++ x.2 = y)
              ) := by
      simp [threemerge, refines]
      intros l l' indis
      rcases indis with ⟨indisL, indisR⟩
      constructor
      . simp_all
        intros ident mid v val pf2
        fin_cases ident <;> simp_all
        · constructor; and_intros
          · apply existSR.done
          · trivial
          · constructor
            · intros ident' new_i v_1 Hrule; simp_all
              fin_cases ident' <;> simp_all
            · intros ident' new_i v_1 HVal; simp_all
              fin_cases ident' <;> simp_all
              cases pf2 
              cases HVal
              subst mid
              subst l'
              subst v
              exists (val :: (l ++ new_i.2))
              simp
        · constructor; and_intros
          · apply existSR.done
          · trivial
          · constructor
            · intros ident' new_i v_1 Hrule; simp_all
              fin_cases ident' <;> simp_all
            · intros ident' new_i v_1 HVal; simp_all
              fin_cases ident' <;> simp_all
              cases pf2 
              
              cases HVal
              subst mid
              subst l'
              subst v
              exists (val :: (l ++ new_i.2))
              simp
        · constructor; and_intros
          · apply existSR.done
          · cases pf2; subst l; subst v
          · constructor
            · intros ident' new_i v_1 Hrule; simp_all
              fin_cases ident' <;> simp_all
            · intros ident' new_i v_1 HVal; simp_all
              fin_cases ident' <;> simp_all
              cases pf2 
              cases HVal
              subst mid
              subst l'
              subst v
              exists (val :: (l ++ new_i.2))
              simp

    -- stop by
    --       simp; constructor<;> simp;
    --       . intros ident
    --         simp [List.remove, threemerge] at *
    --         simp [List.remove] at ident
    --         rcases ident with ⟨i, pf⟩
    --         rcases i with ⟨ ⟨ ⟩ |  jjd  ⟩
    --         simp at *
    --         rename_i i
    --         rcases i with ⟨ ⟨ ⟩ | ⟨ i ⟩ ⟩
    --         simp at *
    --         omega
    --       . intros ident
    --         simp [List.remove, threemerge] at *
section RefinementTheorem

--def inlining (e: ExprLow) (ε : List (T × Module T)) (pf : List.get ε i = )

-- inductive ExprLow where
--   | base : Nat -> ExprLow
--   | product : ExprLow -> ExprLow -> ExprLow
--   | connect : ExprLow -> Nat -> Nat -> ExprLow


end RefinementTheorem


end DataflowRewriter
