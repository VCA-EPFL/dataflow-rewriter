import Leanses
import Lean
import Init.Data.BitVec.Lemmas
import Mathlib

open Lean Meta Elab
namespace DataflowRewriter

structure Module (S : Type u₁) : Type (max u₁ (u₂ + 1)) where
  inputs : List ((T : Type u₂) × (S -> T -> S -> Prop))
  outputs : List ((T : Type u₂) × (S -> T -> S -> Prop))
  internals : List (S -> S -> Prop)

mklenses Module
open Module.l


def empty : Module S := {inputs := [], outputs := [], internals:= []}

-- @[simp]
-- def _root_.List.remove {α : Type u} : (as : List α) → Fin as.length → List α
--   | .cons _ as, ⟨0, _⟩ => as
--   | .cons a as, ⟨i + 1, h⟩ => a :: as.remove ⟨i, Nat.le_of_succ_le_succ h⟩

@[simp]
def _root_.List.remove {α : Type u} (as : List α) (i : Fin as.length) : List α := as.eraseIdx i

def connect (mod : Module S) (i : Fin mod.inputs.length) (o : Fin mod.outputs.length)
      (wf : (mod.inputs.get i).1 = (mod.outputs.get o).1) : Module S :=
       { inputs := mod.inputs.remove i,
         outputs :=  mod.outputs.remove o,
         internals :=  (λ st st' => ∃ consumed_output output, (mod.outputs.get o).2 st output consumed_output ∧
                              (mod.inputs.get i).2 consumed_output (Eq.rec id wf output) st')
                        :: mod.internals }

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
def merge T : Module (List T):=
      { inputs := [⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩,
                   ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩],
        outputs := [⟨ T, λ oldList oldElement newList => ∃ i, newList = oldList.remove i ∧ oldElement = oldList.get i ⟩],
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
  l.getD n (⟨ PUnit, λ _ _ _ => True ⟩)

@[simp]
def getRule {S : Type _} (l : List (S → S → Prop)) (n : Nat) : (S → S → Prop) :=
  l.getD n (λ _ _ => True)

variable (baseModules : Fin n → ((T : Type) × Module T))

structure indistinguishable_strict (imod : Module I) (smod : Module S) : Prop where
  inputs_length : imod.inputs.length = smod.inputs.length
  inputs_types : ∀ ident, (imod.inputs.get ident).1 = (smod.inputs.get (Eq.rec id inputs_length ident)).1

  inputs_indistinguishable : ∀ ident init_i new_i init_s v,
    (imod.inputs.get ident).2 init_i v new_i →
    ∃ new_s,
      (smod.inputs.get (Eq.rec id inputs_length ident)).2 init_s ((inputs_types ident).mp v) new_s

  outputs_length : imod.outputs.length = smod.outputs.length
  outputs_types : ∀ ident, (imod.outputs.get ident).1 = (smod.outputs.get (Eq.rec id outputs_length ident)).1

  outputs_indistinguishable : ∀ ident init_i new_i init_s v,
    (imod.outputs.get ident).2 init_i v new_i →
    ∃ new_s,
      (smod.outputs.get (Eq.rec id outputs_length ident)).2 init_s ((outputs_types ident).mp v) new_s

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

theorem perm_erase {α : Type _} [DecidableEq α] (l₁ l₂ : List α) i:
  l₁.Perm l₂ →
  (l₁.erase i).Perm (l₂.erase i) := by
  intro H; induction H generalizing i with
  | nil => simp
  | cons x l1 l2 => 
    rename_i l1' l2'
    rw [List.erase_cons]
    rw [List.erase_cons]
    split_ifs <;> simp [*]
  | swap x y l =>
    rw [List.erase_cons]
    rw [List.erase_cons]
    rw [List.erase_cons]
    rw [List.erase_cons]
    split_ifs <;> (try simp [*])
    · simp [*] at *
      rename_i H1 H2; rw [H1,H2]
    · simp [*] at *; apply List.Perm.swap
  | trans _ _ H1 H2 =>
    rename_i l₃ _ _
    trans; apply H1; simp [*]

#check List.getElem_append_left

theorem interface_match T :  matching_interface (merge_sem T).snd (threemerge T) := by
  constructor <;> (intro ident; fin_cases ident) <;> rfl

-- #print refines
-- #print indistinguishable
-- set_option pp.proofs true
-- set_option trace.profiler true 
-- -- set_option trace.Meta.Tactic.simp.rewrite true
-- set_option trace.Meta.Tactic.simp.numSteps true
-- set_option pp.proofs.threshold 0
theorem correct_threeway {T: Type _} [DecidableEq T]:
    refines ((merge_sem T).snd) (threemerge T) (interface_match T)
          (fun x y => (x.1 ++ x.2).Perm y) := by
      simp [threemerge, refines]
      intro x1 x2 y He indis
      rcases indis with ⟨indisL, indisR⟩
      constructor <;> dsimp at *
      . intro ident mid_i v Hi
        (fin_cases ident <;> dsimp at *)
        · constructor; constructor; and_intros
          · rfl
          · apply existSR.done
          · rcases Hi with ⟨ Hl, Hr ⟩
            rw [Hl]; subst x2
            simp [*]
          · constructor <;> dsimp only
            · intro ident' new_i v_1 Hrule
              fin_cases ident' <;> simp
            · intros ident' new_i v_1 HVal
              fin_cases ident' <;> simp
              reduce at *
              rcases Hi with ⟨ Hil, Hir ⟩
              rcases HVal with ⟨ ⟨ i, HVall, temp ⟩, HValr ⟩
              subst x2; subst v_1
              generalize h : mid_i.2.get i = y'
              have Ht : ∃ i, mid_i.2.get i = y' := by exists i
              rw [← List.mem_iff_get] at Ht
              have Hiff := List.Perm.mem_iff (a := y') He
              have Ht' : y' ∈ y := by rw [← Hiff]; simp; tauto
              rw [List.mem_iff_get] at Ht'
              rcases Ht' with ⟨ i', Ht'r ⟩
              constructor; exists i' + 1
              simp; tauto
        · constructor; constructor; and_intros
          · rfl
          · apply existSR.done
          · rcases Hi with ⟨ Hl, Hr ⟩
            rw [Hl]; subst x2
            simp [*]
          · constructor
            · intros ident' new_i v_1 Hrule
              fin_cases ident' <;> simp
            · intros ident' new_i v_1 HVal
              fin_cases ident' <;> simp
              reduce at *
              rcases Hi with ⟨ Hil, Hir ⟩
              rcases HVal with ⟨ ⟨ i, HVall, temp ⟩, HValr ⟩
              subst x2; subst v_1
              generalize h : mid_i.2.get i = y'
              have Ht : ∃ i, mid_i.2.get i = y' := by exists i
              rw [← List.mem_iff_get] at Ht
              have Hiff := List.Perm.mem_iff (a := y') He
              have Ht' : y' ∈ y := by rw [← Hiff]; simp; tauto
              rw [List.mem_iff_get] at Ht'
              rcases Ht' with ⟨ i', Ht'r ⟩
              constructor; exists i' + 1
              simp; tauto
        · constructor; constructor; and_intros
          · rfl
          · apply existSR.done
          · rcases Hi with ⟨ Hl, Hr ⟩
            rw [Hl]; subst x1
            rw [List.perm_comm]
            apply List.perm_cons_append_cons; rw [List.perm_comm]; assumption
          · constructor
            · intros ident' new_i v_1 Hrule
              fin_cases ident' <;> simp
            · intros ident' new_i v_1 HVal
              fin_cases ident' <;> simp
              reduce at *
              rcases Hi with ⟨ Hil, Hir ⟩
              rcases HVal with ⟨ ⟨ i, HVall, temp ⟩, HValr ⟩
              subst x1; subst v_1
              generalize h : mid_i.2.get i = y'
              have Ht : ∃ i', mid_i.2.get i' = y' := by exists i
              rw [← List.mem_iff_get] at Ht
              -- FAILS???: rw [Hil] at Ht
              have Ht' : y' ∈ v :: x2 := by rw [← Hil]; assumption
              rcases Ht' with _ | Ht'
              · constructor; exists 0
              · rename_i Ht';
                have Hiff := List.Perm.mem_iff (a := y') He
                have : y' ∈ y := by rw [← Hiff]; simp; tauto
                rw [List.mem_iff_get] at this
                rcases this with ⟨ i, Hl ⟩
                constructor; exists i + 1
                simp; tauto
      . stop intro ident mid_i v Hi
        fin_cases ident <;> dsimp only at * <;> reduce at *
        rcases Hi with ⟨ ⟨ i, Hil ⟩, Hir ⟩
        reduce at *
        rcases Hil with ⟨ Hill, Hilr ⟩
        subst v; subst x1
        generalize Hx2get : x2.get i = v'
        have Hx2in : v' ∈ x2 := by rw [List.mem_iff_get]; tauto
        have Hiff := List.Perm.mem_iff (a := v') He
        have Hyin : v' ∈ y := by rw [← Hiff]; simp; tauto
        rw [List.mem_iff_get] at Hyin
        rcases Hyin with ⟨ i', Hyget ⟩
        constructor; constructor; and_intros
        · exists i'; and_intros; rfl; tauto
        · apply existSR.done
        · rw [Hill]; simp
          sorry
        · constructor <;> dsimp only
          · intro ident' new_i v_1 Hrule
            fin_cases ident' <;> simp
          · intros ident' new_i v_1 HVal
            fin_cases ident' <;> simp
            reduce at *
            rcases HVal with ⟨ ⟨ i'', HVall, temp ⟩, HValr ⟩
            subst v'; subst v_1
            sorry
      · intro ident mid_i Hv
        fin_cases ident
        rcases Hv with ⟨ la, lb, vout, ⟨ ⟨ i, H2, H3 ⟩, Hx3 ⟩, ⟨ Hx2, H4 ⟩ ⟩; subst lb; subst la; subst vout
        constructor; and_intros
        · apply existSR.done
        · rw [Hx2,← H4,←List.eraseIdx_append_of_lt_length] <;> [skip; apply i.isLt]
          dsimp only; 
          trans ((x1 ++ x1[i] :: x2).erase x1[i])
          rw [List.perm_comm]
          have : x1[↑i] = x1.get i := by simp
          simp [*] at *
          have H : x1[↑i] = (x1 ++ x1[↑i] :: x2)[↑i] := by
            symm; apply List.getElem_append_left
          dsimp at *; conv => arg 1; arg 2; rw [H]
          apply List.erase_get
          trans ((x1[i] :: (x1 ++ x2)).erase x1[i])
          apply perm_erase; simp
          rw [List.erase_cons_head]; assumption
        · constructor
          · intros ident' new_i v_1 Hrule
            fin_cases ident' <;> simp
          · intros ident' new_i v_1 HVal
            fin_cases ident' <;> simp
            reduce at *
            rcases HVal with ⟨ ⟨ i', HVall, temp ⟩, HValr ⟩
            subst v_1
            generalize h : mid_i.2.get i' = y'
            have Ht : ∃ i', mid_i.2.get i' = y' := by exists i'
            rw [← List.mem_iff_get] at Ht
            have Hiff := List.Perm.mem_iff (a := y') He
            have Ht'' : y' ∈ x1.get i :: x2 := by rw [←Hx2]; assumption
            simp at Ht''; rcases Ht'' with (Ht'' | Ht'')
            · 
            have Ht' : y' ∈ y := by rw [← Hiff]; simp; tauto
            rcases Ht' with _ | Ht'
            · constructor; exists 0
            · rename_i Ht';
              have Hiff := List.Perm.mem_iff (a := y') He
              have : y' ∈ y := by rw [← Hiff]; simp; tauto
              rw [List.mem_iff_get] at this
              rcases this with ⟨ i, Hl ⟩
              constructor; exists i + 1
              simp; tauto
          
            -- generalize h : mid_i.2.get i' = y'
            
            -- have Ht : ∃ i, mid_i.2.get i = y' := by exists i'
            -- rw [← List.mem_iff_get] at Ht
            -- have Hiff := List.Perm.mem_iff (a := y') He
            -- have : y' ∈ y := by rw [← Hiff]; simp; tauto
            -- rw [List.mem_iff_get] at Ht'
            -- rcases Ht' with ⟨ i', Ht'r ⟩
            -- constructor; exists i' + 1
            -- simp; tauto
                

-- theorem correct_threeway' {T: Type _} :
--     refines ((merge_sem T).snd) (threemerge T) (lol T)
--           (fun x y => by
--               simp at x;
--               exact (x.1 ++ x.2 = y)
--               ) := by
--       simp [threemerge, refines]
--       intros l l' indis
--       rcases indis with ⟨indisL, indisR⟩
--       constructor
--       . simp_all
--         intros ident mid v val pf2
--         fin_cases ident <;> simp_all
--         · constructor; and_intros
--           · apply existSR.done
--           · trivial
--           · constructor
--             · intros ident' new_i v_1 Hrule; simp_all
--               fin_cases ident' <;> simp_all
--             · intros ident' new_i v_1 HVal; simp_all
--               fin_cases ident' <;> simp_all
--               cases pf2 
--               cases HVal
--               subst mid
--               subst l'
--               subst v
--               exists (val :: (l ++ new_i.2))
--               simp
--         · constructor; and_intros
--           · apply existSR.done
--           · trivial
--           · constructor
--             · intros ident' new_i v_1 Hrule; simp_all
--               fin_cases ident' <;> simp_all
--             · intros ident' new_i v_1 HVal; simp_all
--               fin_cases ident' <;> simp_all
--               cases pf2 
              
--               cases HVal
--               subst mid
--               subst l'
--               subst v
--               exists (val :: (l ++ new_i.2))
--               simp

    -- stop by
    --       simp; constructor<;> simp;
    --       . intros ident
    --         simp [List.remove, threemerge] at *
e     --         simp [List.remove] at ident
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
