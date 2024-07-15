namespace DataflowRewriter

/--
Create a class for an arbitrary state transition system.
-/
class StateTransition (Event: Type _) (State: Type _) where
  init : State
  step : State -> List Event -> State -> Prop

/--
These are notations, which allow you to have nicer syntax when you write
theorems.  We don't have to use them though, so below I've just left it as
normal function syntax.
-/
notation:45 s " -[ " t:45 " ]-> " s':44 => StateTransition.step s t s'

section

variable {State Event : Type}

-- Variable of type StateTransition which needs Event and State for its constructor
variable [trans: StateTransition Event State]

-- It will trigger an inductive hypothesis, reflexive tranisitve closure
inductive star : State -> List Event -> State -> Prop where
  -- this performs no steps ([]) keeping us in the same state s1. It is the base case of induction and models the reflexive property (s1 is equal to itself)
  | refl : forall s1, star s1 [] s1
  -- this states the transitive property, if s1 takes you to s2 through e1 and s2 takes you to s3 through e2. Then, we can go from s1 to s3 directly by concatenating e1 and e2.
  | step : forall s1, trans.step s1 e1 s2 -> star s2 e2 s3 -> star s1 (e1 ++ e2) s3

notation:45 s " -[ " t:45 " ]*> " s':44 => star s t s'

def behaviour (l : List Event): Prop :=
  exists s', star trans.init l s'

theorem star.plus_one (s s': State) (e: List Event) :
    s -[e]-> s' -> s -[e]*> s' := by
  intros Hstep
  have He : e = e ++ [] := by simp
  rw [He]
  apply star.step <;> first | assumption | apply star.refl

  theorem star.trans_star (s s' s'': State) (e e': List Event) :
    s -[e]*> s' -> s' -[e']*> s'' -> s -[e ++ e']*> s''  := by
    intros H1; induction H1 generalizing s'' e'
    . simp
    . intros H1
      rw [List.append_assoc]
      apply star.step
      assumption
      rename_i ih
      apply ih; apply H1

theorem step_internal [trans : StateTransition a b] :
  ∀ s1, trans.step s1 [] s2 -> star s2 e2 s3 -> @star _ _ trans s1 e2 s3 := by
  have h : e2 = [] ++ e2 := by rfl
  intros; rw [h]
  apply star.step <;> assumption

theorem step_one [trans : StateTransition a b] :
  ∀ s1, trans.step s1 e2 s2 -> @star _ _ trans s1 e2 s2 := by
  have h : e2 = e2 ++ [] := by simp
  intros; rw [h]
  apply star.step <;> first | assumption | apply star.refl

end

-- Functions are produced with the fun syntax that begins with the keyword fun
-- followed by one or more arguments, which are separated from the return expression using => .
-- In this function, i is the argument and the return expression is the entire code coming after =>
-- Fin is a positive natural number
-- (1) a is an arbitrary type, (2) i' is a positive natural number, (3) f has a function syntax from n to a
-- The retrun type of the function comes after the colon (:) and in this case the return is a function from n to a
def update_Fin {a: Type} (i' : Fin n)  (e : a) (f : Fin n -> a) : Fin n -> a :=
  fun i =>
    if i == i' then
      e
    else
      f i

@[simp]
theorem update_Fin_gso {a: Type} (i i' : Fin n)  (e : a) (f : Fin n -> a) :
  ¬(i = i') -> update_Fin i' e f i = f i := by
    intro h1
    unfold update_Fin
    simp [*] at *


@[simp]
theorem update_Fin_gss {a: Type} (i  : Fin n)  (e : a) (f : Fin n -> a) :
  update_Fin i e f i  = e := by
    unfold update_Fin
    simp

def enq_Fin {a: Type} (i' : Fin n)  (e : a) (f : Fin n -> List a) : Fin n -> List a :=
  fun i =>
    if i == i' then
      f i ++ [e]
    else
      f i

def subtract_Fin (i : Fin 3): Fin 2 :=
  match i with
  | 0 => 0
  | 1 => 0
  | 2 => 1

abbrev Token := Nat
abbrev Port2 := Fin 2
abbrev Port3 := Fin 3
abbrev Queue := List Token

inductive Event size where
  | write_port (v : Token)
  | read_port (n : Fin size) (v : Token)
  deriving Inhabited, Repr

def range (n : Nat) : List (Fin n) :=
  loop n (Nat.le_of_eq (Eq.refl n)) []
where
  loop : (y:Nat) → y <= n → List (Fin n) → List (Fin n)
  | 0,   _,  ns => ns
  | n+1, lt, ns => let ltn := Nat.lt_of_succ_le lt; loop n (Nat.le_of_lt ltn) ({val := n, isLt := ltn}::ns)

instance [Repr b] : Repr (Fin n → b) where
  reprPrec a _n := Id.run <| do
    let mut s : Std.Format := ""
    for nVal in range n do
      s := s ++ (repr <| a nVal)
    return s

end DataflowRewriter
