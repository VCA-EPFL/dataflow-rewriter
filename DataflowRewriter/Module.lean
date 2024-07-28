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
  deriving Repr

structure Connection where
  inputInstance  : Nat
  outputInstance : Nat
  inputPort      : Nat
  outputPort     : Nat
  deriving Repr

structure Interface where
  inputs : Nat
  outputs : Nat
  deriving Repr

structure ExprHigh where
  modules     : List Nat
  connections : List Connection
  deriving Repr

/--
Returns the maximum number of input and output ports for each module.
-/
-- def maxPorts (l : ExprHigh) : List (Nat × Nat) :=
--   Id.run <| do
--     let mut outL : List (Nat × Nat) := []
--     for mod in List.range (l.modules.length) do
--       let mut max_out := 0
--       let mut max_in := 0
--       for conn in l.connections do
--         match conn with
--         | .connect inputInstance outputInstance inputPort outputPort =>
--           if mod = inputInstance then max_in := max_in.max inputPort
--           if mod = outputInstance then max_out := max_out.max outputPort
--         | .dangleInput inst port => if mod = inst then max_in := max_in.max port
--         | .dangleOutput inst port => if mod = inst then max_out := max_out.max port
--       outL := outL ++ [(max_in, max_out)]
--     return outL

def accumUntil (ports : List Interface) (n : Nat): Nat × Nat :=
  (ports.foldl (λ a b => if a.fst < n then (a.fst + 1, a.snd + (b.inputs, b.outputs)) else a) (0, 0, 0)).snd

def findInput (ports : List Interface) (n : Nat): Nat × Nat :=
  let (a, b, _) := ports.foldl (λ (a : Nat × Nat × Bool) b =>
    if a.2.1 + b.inputs <= n && a.2.2
    then (a.1 + 1, a.2.1 + b.inputs, a.2.2)
    else if a.2.1 <= n && a.2.1 + b.inputs > n && a.2.2
         then (a.1, n - a.2.1, false)
         else a) (0, 0, true)
  (a, b)

def findOutput (ports : List Interface) (n : Nat): Nat × Nat :=
  let (a, b, _) := ports.foldl (λ (a : Nat × Nat × Bool) b =>
    if a.2.1 + b.outputs <= n && a.2.2
    then (a.1 + 1, a.2.1 + b.outputs, a.2.2)
    else if a.2.1 <= n && a.2.1 + b.outputs > n && a.2.2
         then (a.1, n - a.2.1, false)
         else a) (0, 0, true)
  (a, b)

def connectWithOffset (ports : List Interface) (prod : ExprLow) (conn : Connection) : Option ExprLow := do
  let inputOffs := accumUntil ports conn.inputInstance
  let outputOffs := accumUntil ports conn.outputInstance
  let newProd := ExprLow.connect prod (inputOffs.fst + conn.inputPort) (outputOffs.snd + conn.outputPort)
  return newProd

def getEachInterface (i : List Interface) (e : ExprHigh) := sequence <| e.modules.map (i.get? ·)

def lower (i : List Interface) (e : ExprHigh) : Option ExprLow := do
  match e.modules with
  | m :: ms =>
    let prod := (ms.map (ExprLow.base ·)).foldl ExprLow.product (ExprLow.base m)
    e.connections.foldlM (connectWithOffset <| ← getEachInterface i e) prod
  | _ => none

def higher (i : List Interface) (e : ExprLow) : Option ExprHigh := do
  match e with
  | .base n => pure ⟨ [ n ], [] ⟩
  | .product a b =>
    let ha ← higher i a
    let hb ← higher i b
    pure ⟨ ha.modules ++ hb.modules, ha.connections ++ hb.connections ⟩
  | .connect a ni no =>
    let ha ← higher i a
    let eachInt ← getEachInterface i ha
    let inp := findInput eachInt ni
    let out := findOutput eachInt no
    pure ⟨ ha.modules, ⟨ inp.1, out.1, inp.2, out.2 ⟩ :: ha.connections ⟩

declare_syntax_cat dot_value
declare_syntax_cat dot_stmnt
declare_syntax_cat dot_attr_list
declare_syntax_cat dot_attr

syntax str : dot_value
syntax num : dot_value
syntax ident : dot_value

syntax ident " = " dot_value : dot_attr
syntax (dot_attr),* : dot_attr_list

syntax ident (" [" dot_attr_list "]")? : dot_stmnt
syntax ident " -> " ident (" [" dot_attr_list "]")? : dot_stmnt

syntax dot_stmnt_list := (dot_stmnt "; ")*

syntax (name := dot_graph) "[graph| " dot_stmnt_list " ]" : term

#check_failure [graph| a [node = 0, n2 = 1]; b; c; a -> c; ]

set_option pp.rawOnError true

open Term Syntax

def findStx (n : Name) (stx : Array Syntax) : Option Nat := do
  let mut out := none
  for pair in stx do
    if pair[0].getId = n then
      out := some (TSyntax.mk pair[2][0]).getNat
  out

@[term_elab dot_graph]
def dotGraphElab : TermElab := λ stx typ? => do
  let mut idx := 0
  let mut hmap : HashMap Name (Nat × Nat) := mkHashMap
  let mut conns : List Connection := []
  for stmnt in stx[1][0].getArgs do
    let low_stmnt := stmnt.getArgs[0]!
    match low_stmnt with
    -- | `(dot_stmnt| $i:ident $[[$[$el:dot_attr],*]]? ) =>
    | `(dot_stmnt| $i:ident $[[$[$el:dot_attr],*]]? ) =>
      let mut modId: Nat := 0
      if el.isSome then
        modId := (findStx `mod (← el)).getD 0
      let (map', idx') := hmap.insertIfNew i.getId (idx, modId)
      if idx'.isNone then
        hmap := map'; idx := idx + 1
      -- logInfo m!"{el.map (·.get! 1 |>.raw.getArgs.get! 0)}"
    | `(dot_stmnt| $a:ident -> $b:ident $[[$[$el:dot_attr],*]]? ) =>
      let mut out := 0
      let mut inp := 0
      if el.isSome then
        let el ← el
        out := (findStx `out el).getD 0
        inp := (findStx `inp el).getD 0
      let inpMod := hmap.find! b.getId
      let outMod := hmap.find! a.getId
      -- logInfo m!"out = {out}, in = {inp}"
      conns := ⟨ inpMod.1, outMod.1, inp, out ⟩ :: conns
    | _ => pure ()
  let lst := ((hmap.toArray.map (·.snd)).insertionSort (fun (a, _) (a', _) => a <= a')).toList.map (·.snd)
  -- logInfo m!"{lst}"
  let connExpr ← mkListLit (mkConst ``Connection) (← conns.mapM (λ ⟨ a, b, c, d ⟩ => do
    let s ← #[a, b, c, d].mapM (mkNumeral (mkConst ``Nat) ·)
    mkAppM ``Connection.mk s))
  let modList ← mkListLit (mkConst ``Nat) (← lst.mapM (mkNumeral (mkConst ``Nat) ·))
  mkAppM ``ExprHigh.mk #[modList, connExpr]

def merge3 : ExprHigh :=
  [graph|
    merge1 [label="merge1"];
    merge2;
    merge1 -> merge2;
  ]

#eval lower [ ⟨ 2, 1 ⟩ ] merge3

def highlow int mod := do
  higher int <| ← lower int mod

#eval highlow [ ⟨ 2, 1 ⟩ ] merge3

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

theorem interface_match T :  matching_interface (merge_sem T).snd (threemerge T) := by
  constructor <;> (intro ident; fin_cases ident) <;> rfl

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
              fin_cases ident'; simp
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
              fin_cases ident'; simp
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
              fin_cases ident'; simp
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
      . intro ident mid_i v Hi
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
        have HerasePerm : (mid_i.1.append mid_i.2).Perm (y.eraseIdx i'.1) := by
          simp [Hill]
          trans; apply List.perm_append_comm
          rw [←List.eraseIdx_append_of_lt_length] <;> [skip; apply i.isLt]
          trans ((x2 ++ mid_i.1).erase x2[i])
          have H2 : x2[i] = (x2 ++ mid_i.1)[i] := by
            symm; apply List.getElem_append_left
          rw [H2]; symm; apply List.erase_get
          symm; trans; symm; apply List.erase_get
          rw [Hyget]; simp at Hx2get; simp; rw [Hx2get]
          apply perm_erase; symm
          symm; trans; symm; assumption
          apply List.perm_append_comm
        constructor; constructor; and_intros
        · exists i'; and_intros; rfl; tauto
        · apply existSR.done
        · assumption
        · constructor <;> dsimp only
          · intro ident' new_i v_1 Hrule
            fin_cases ident' <;> simp
          · intros ident' new_i v_1 HVal
            fin_cases ident'
            reduce at *
            rcases HVal with ⟨ ⟨ i'', HVall, temp ⟩, HValr ⟩
            subst v'; subst v_1
            dsimp at *
            have : mid_i.2[i''] ∈ (x2.eraseIdx i.1) := by
              simp [Hill]; apply List.getElem_mem
            have : mid_i.2[i''] ∈ (mid_i.1 ++ x2.eraseIdx i.1) := by
              rw [List.mem_eraseIdx_iff_getElem] at this; simp; right
              simp at *; simp [Hill]; apply List.getElem_mem
            have HPermIn : mid_i.2[i''] ∈ y.eraseIdx i' := by
              rw [List.Perm.mem_iff]; assumption; symm
              rw [←Hill]; assumption
            rw [List.mem_iff_getElem] at HPermIn
            rcases HPermIn with ⟨ Ha, Hb, Hc ⟩
            constructor; exists ⟨ Ha, Hb ⟩; tauto
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
            fin_cases ident'
            reduce at *
            rcases HVal with ⟨ ⟨ i', _, temp ⟩, _ ⟩
            subst v_1
            generalize h : mid_i.2.get i' = y'
            have Ht : ∃ i', mid_i.2.get i' = y' := by exists i'
            rw [← List.mem_iff_get] at Ht
            have Hiff := List.Perm.mem_iff (a := y') He
            have Ht'' : y' ∈ x1.get i :: x2 := by rw [←Hx2]; assumption
            simp at Ht''; rcases Ht'' with (Ht'' | Ht'')
            · have Ht' : y' ∈ y := by
                rw [List.Perm.mem_iff]; rotate_left; rewrite [List.perm_comm]; assumption; subst y'
                rw [Ht'']; simp; left; apply List.getElem_mem
              dsimp; apply List.getElem_of_mem at Ht'; rcases Ht' with ⟨ Ha, Hb, Hc ⟩
              constructor; exists ⟨ Ha, Hb ⟩; and_intros; rfl; symm; assumption
            · have Ht' : y' ∈ y := by
                rw [List.Perm.mem_iff]; rotate_left; rewrite [List.perm_comm]; assumption; subst y'
                simp; tauto
              dsimp; apply List.getElem_of_mem at Ht'; rcases Ht' with ⟨ Ha, Hb, Hc ⟩
              constructor; exists ⟨ Ha, Hb ⟩; and_intros; rfl; symm; assumption

section RefinementTheorem

end RefinementTheorem


end DataflowRewriter
