import DataflowRewriter.StateTransition

namespace DataflowRewriter

structure ForkState where
  input_queue : Queue
  output_queues : Fin 2 → Queue
  deriving Inhabited, Repr

inductive step_fork : ForkState → List (Event 2) → ForkState → Prop where
  | handle_write_event : ∀ s v,
    step_fork s [Event.write_port v] { s with input_queue := s.input_queue ++ [v] }
  | handle_read_event : ∀ s n v rst,
    s.output_queues n = v :: rst →
    step_fork s [Event.read_port n v] { s with output_queues := update_Fin n rst s.output_queues }
  | internal_step : ∀ s v rst,
    s.input_queue = v :: rst →
    step_fork s [] { s with output_queues := enq_Fin 0 v (enq_Fin 1 v s.output_queues),
                            input_queue := rst 
                   }

instance : StateTransition (Event 2) ForkState where
  init := default
  step := step_fork

structure DoubleForkState where
  fork1 : ForkState
  fork2 : ForkState
  deriving Inhabited, Repr

inductive step_double_fork : DoubleForkState → List (Event 3) → DoubleForkState → Prop where
  | handle_write_event : ∀ s fork1' v,
    step_fork s.fork1 [Event.write_port v] fork1' →
    step_double_fork s [Event.write_port v] { s with fork1 := fork1' }
  | handle_read_event1 : ∀ s fork1' v,
    step_fork s.fork1 [Event.read_port 0 v] fork1' →
    step_double_fork s [Event.read_port 0 v] { s with fork1 := fork1' }
  | handle_read_event2 : ∀ s fork2' (n : Fin 3) v,
    n ≠ 0 →
    step_fork s.fork2 [Event.read_port (subtract_Fin n) v] fork2' →
    step_double_fork s [Event.read_port n v] { s with fork2 := fork2' }
  | run_internal_fork1 : ∀ s fork1',
    step_fork s.fork1 [] fork1' →
    step_double_fork s [] { s with fork1 := fork1' }
  | run_internal_fork2 : ∀ s fork2',
    step_fork s.fork2 [] fork2' →
    step_double_fork s [] { s with fork2 := fork2' }
  | push_internal_token : ∀ s v fork1' fork2',
    step_fork s.fork1 [Event.read_port 1 v] fork1' →
    step_fork s.fork2 [Event.write_port v] fork2' →
    step_double_fork s [] { s with fork1 := fork1',
                                   fork2 := fork2'
                          }

instance : StateTransition (Event 3) DoubleForkState where
  init := default
  step := step_double_fork

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

theorem can_reach_some_output :
  ∃ s', { (default : DoubleForkState) with fork1.input_queue := [5] } 
          -[ [(Event.read_port 2 5 : Event 3)] ]*> s' := by
    simp [default]; constructor
    apply step_internal
    · apply step_double_fork.run_internal_fork1
      apply step_fork.internal_step
      and_intros <;> rfl
    · apply step_internal
      · apply step_double_fork.push_internal_token
        apply step_fork.handle_read_event
        · unfold enq_Fin; simp
          and_intros <;> rfl
        · apply step_fork.handle_write_event
      · apply step_internal
        · apply step_double_fork.run_internal_fork2
          apply step_fork.internal_step
          simp; and_intros <;> rfl
        · apply step_one
          apply step_double_fork.handle_read_event2
          · omega
          · have h : subtract_Fin 2 = 1 := by simp [subtract_Fin]
            simp; rw [h]
            apply step_fork.handle_read_event
            simp [enq_Fin]; rfl

end DataflowRewriter
