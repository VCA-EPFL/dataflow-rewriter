import DataflowRewriter.StateTransition

namespace DataflowRewriter

inductive Method where
  | enq (n : Nat)
  | deq (n : Nat)
  | lock
  | unlock

structure ImpState where
  lock : Bool
  queue : Queue
  deriving Inhabited, Repr

inductive imp_step : ImpState → List Method → ImpState → Prop where
  | handle_enq : ∀ s n,
    s.lock = false →
    imp_step s [Method.enq n] { s with queue := s.queue ++ [n] }
  | handle_deq : ∀ s n rst,
    s.queue = n :: rst →
    imp_step s [Method.deq n] { s with queue := rst }
  | handle_lock : ∀ s,
    imp_step s [Method.lock] { s with lock := true }
  | handle_unlock : ∀ s,
    imp_step s [Method.unlock] { s with lock := false }
  | unlock_natural : ∀ s,
    s.queue = [] →
    imp_step s [] { s with lock := false }

instance ImpStateTransition : StateTransition Method ImpState where
  init := default
  step := imp_step

structure SpecState where
  queue : Queue
  deriving Inhabited, Repr

inductive spec_step : SpecState → List Method → SpecState → Prop where
  | handle_enq : ∀ s n,
    spec_step s [Method.enq n] { s with queue := s.queue ++ [n] }
  | handle_deq : ∀ s n rst,
    s.queue = n :: rst →
    spec_step s [Method.deq n] { s with queue := rst }
  | handle_lock : ∀ s,
    spec_step s [Method.lock] s
  | handle_unlock : ∀ s,
    spec_step s [Method.unlock] s

instance SpecStateTransition : StateTransition Method SpecState where
  init := default
  step := spec_step

section

variable {ImpState SpecState : Type}

variable [imp : StateTransition Method ImpState]
variable [spec : StateTransition Method SpecState]

def indistinguishable (i: ImpState) (s: SpecState): Prop :=
  ∀ (e: List Method) i', i -[e]-> i' → ∃ s', s -[e]-> s'

infix:60 " ≺ " => indistinguishable

end

inductive φ : ImpState → SpecState → Prop where
  | base :
    φ ⟨false, []⟩ ⟨[]⟩
  | enq : ∀ i (i' : Nat → ImpState) s (s' : Nat → SpecState),
    (∀ n, i' n = { i with queue := i.queue ++ [n] }) →
    (∀ n, s' n = { s with queue := s.queue ++ [n] }) →
    (∀ n, φ (i' n) (s' n)) →
    (∀ n, imp_step i [Method.enq n] (i' n)) →
    (∀ n, spec_step s [Method.enq n] (s' n)) →
    φ i s
  | deq : ∀ i i' s s',
    φ i' s' →
    imp_step i [Method.deq n] i' →
    spec_step s [Method.deq n] s' →
    φ i s
  | unlock : ∀ i i' s s',
    φ i' s' →
    imp_step i [Method.unlock] i' →
    spec_step s [Method.unlock] s' →
    φ i s
  | lock : ∀ i i' s s',
    φ i' s' →
    imp_step i [Method.lock] i' →
    spec_step s [Method.lock] s' →
    φ i s
  | internal : ∀ i i' s,
    φ i' s →
    imp_step i [] i' →
    φ i s

theorem enough :
  ∀ i s, φ i s → 
    ∀ e i', imp_step i e i' → 
      ∃ s', star s e s' ∧ φ i' s' := by
  intros i s h; 
  induction h with
  | base =>
    intros e i' Himp
    cases Himp with
    | handle_enq n a =>
      simp; exists ⟨[n]⟩; and_intros
      · apply step_one; constructor
      · apply φ.deq
        · apply φ.base
        · constructor; simp; rfl
        · constructor; simp
    | handle_deq n rst a => simp at a
    | handle_lock =>
      simp; exists ⟨[]⟩; and_intros
      · apply star.plus_one; constructor
      · apply φ.unlock; apply φ.base
        · constructor
        · constructor
    | handle_unlock =>
      simp; exists ⟨[]⟩; and_intros
      · apply star.plus_one; constructor
      · apply φ.base
    | unlock_natural a =>
      simp; exists ⟨[]⟩; and_intros
      · apply star.refl
      · apply φ.base
  | enq i i_ne s s_ne i_wf s_wf Hphi HimpRight HspecRight iH =>
    intros e i_sw HimpDown
    have HimpDown' := HimpDown
    cases HimpDown with
    | handle_enq n' Hlock =>
      exists { s with queue := s.queue ++ [n'] }; and_intros
      · apply star.plus_one; constructor
      · rw [←i_wf,←s_wf]; apply Hphi
    | handle_deq n' rst Hqueue =>
      let Himp2' : ∀ n, imp_step (i_ne n) [Method.deq n'] _ := by
        intros n''; rw [i_wf, Hqueue]; constructor; simp; rfl
      have Himp2 := Himp2'; clear Himp2'
      simp at *
      let iH' : ∀ n, ∃ s', s_ne n -[ [Method.deq n'] ]*> s' ∧ φ { lock := i.lock, queue := rst ++ [n] } s' := by
        intros n''; apply iH
        apply Himp2
      have iH'' := iH'; clear iH'
      rcases s with ⟨ queue ⟩
      rcases queue with _ | ⟨ a, b ⟩
      
      constructor; and_intros
      

end DataflowRewriter
