import DataflowRewriter.StateTransition

namespace DataflowRewriter

-- Aya: Some helpful facts about Lean
/-
(1) An inductive type is built up from a specified list of constructors. In Lean, the syntax for specifying such a type is as follows, where each constructor specifies a way of building new objects of foo, possibly from previously constructed values

inductive foo : Type :=
| constructor₁ : ... → foo
| constructor₂ : ... → foo
...
| constructorₙ : ... → foo

(2)

-/


/--
This is the main state of a fork that produces 2 outputs, it consists of the input and output queues,
which are just lists of tokens (natural numbers).
-/
structure Fork_2_State where
  input_queue : Queue
  output_queues : Fin 2 → Queue  -- Aya: I guess this means we want 2 Queues
  deriving Inhabited, Repr  -- Aya: not sure what is the purpose of this line?

/--
Aya: modeling the structure of a fork that has 3 outputs
-/
structure Fork_3_State where
  input_queue : Queue
  output_queues : Fin 3 → Queue  -- Aya: I guess this means we want 3 Queues
  deriving Inhabited, Repr  -- Aya: not sure what is the purpose of this line?

/--
We now construct a state for the larger system, which combines the 2 2-output forks
into the greater fork, which should then be equivalent with a fork with 3
outputs.

Here we can reuse the fork states of the forks themselves, so that in the
semantics we can reuse the semantics of a single fork.
-/
structure DoubleForkState where
  -- Aya: 2 instances of the above Fork_2_State
  fork1 : Fork_2_State
  fork2 : Fork_2_State
  deriving Inhabited, Repr -- Aya: not sure what is the purpose of this line?


/--
The semantics of a fork with one input and two outputs.  There are three rules,
two rules deal with IO and one rule is an internal transition from the internal
input queue to both output queues.

Note: In the semantics, just to make it easier to fit into the [StateTransition]
framework, IO events are actually lists, but should only really represent an
event (list of one event) or an empty event (empty list).

In addition to that, internal transitions (that don't output an event) and
external transitions (that are observable and output an event) are both defined
in the same set of rules, but they could also be separated out.
-/
-- Aya: Models a transition from one fork state to another through a list of Events that have 2 output ports
inductive step_2_fork : Fork_2_State → List (Event 2) → Fork_2_State → Prop where
  | handle_write_event : ∀ s v,  -- Aya: for every event s receving a token v,
    step_2_fork s [Event.write_port v] { s with input_queue := s.input_queue ++ [v] }  -- Aya: upon a write event, add the token v into the input queue
  | handle_read_event : ∀ s n v rst,  -- Aya for every event s receiving a token v and rst on output queues n
    s.output_queues n = v :: rst → -- Aya: I guess v :: rst symbolizes a list whose first elements come from v then the rest is rst (which probably symbolizes and empty queue?)
    step_2_fork s [Event.read_port n v] { s with output_queues := update_Fin n rst s.output_queues }
  | internal_step : ∀ s v rst,
    s.input_queue = v :: rst →
    step_2_fork s [] { s with output_queues := enq_Fin 0 v (enq_Fin 1 v s.output_queues), input_queue := rst }  -- Aya: I guess this signals the pathway of the token as it moves from the global input queue to the internal queue indicating that the global input queue has become empty

/--
Aya: Models a transition from one fork state to another through a list of Events that have 3 output ports
-/
inductive step_3_fork : Fork_3_State → List (Event 3) → Fork_3_State → Prop where
| handle_write_event : ∀ s v,
    step_3_fork s [Event.write_port v] { s with input_queue := s.input_queue ++ [v] }
| handle_read_event : ∀ s n v rst,
    s.output_queues n = v :: rst →
    step_3_fork s [Event.read_port n v] { s with output_queues := update_Fin n rst s.output_queues }
| internal_step : ∀ s v rst,
    s.input_queue = v :: rst →
    step_3_fork s [] { s with output_queues := enq_Fin 0 v (enq_Fin 1 v s.output_queues), input_queue := rst}

/--
We then define the semantics for the double fork, where we handle write events
by passing them to the first fork, and handle read events by reading from either
fork output depending on the value of the port one wants to read from.
-/
inductive step_double_fork : DoubleForkState → List (Event 3) → DoubleForkState → Prop where
/--
Push a token to the port of fork1.
-/
  | handle_write_event : ∀ s fork1' v,
    step_2_fork s.fork1 [Event.write_port v] fork1' →
    step_double_fork s [Event.write_port v] { s with fork1 := fork1' }
/--
Read a token from the external port of fork1 (port 0).
-/
  | handle_read_event1 : ∀ s fork1' v,
    step_2_fork s.fork1 [Event.read_port 0 v] fork1' →
    step_double_fork s [Event.read_port 0 v] { s with fork1 := fork1' }
/--
Read a token from the external ports of fork2 (port 1 and 2).
-/
  | handle_read_event2 : ∀ s fork2' (n : Fin 3) v,
    n ≠ 0 →
    step_2_fork s.fork2 [Event.read_port (subtract_Fin n) v] fork2' →
    step_double_fork s [Event.read_port n v] { s with fork2 := fork2' }
/--
Run an internal step of fork1.
-/
  | run_internal_fork1 : ∀ s fork1',
    step_2_fork s.fork1 [] fork1' →  -- Aya: what does s.fork1 [] fork1' mean?
    step_double_fork s [] { s with fork1 := fork1' }
/--
Run an internal step of fork2.
-/
  | run_internal_fork2 : ∀ s fork2',
    step_2_fork s.fork2 [] fork2' →
    step_double_fork s [] { s with fork2 := fork2' }
/--
Push a token from the port of fork1 to the input port of fork2.
-/
  | push_internal_token : ∀ s v fork1' fork2',
    step_2_fork s.fork1 [Event.read_port 1 v] fork1' →
    step_2_fork s.fork2 [Event.write_port v] fork2' →
    step_double_fork s [] { s with fork1 := fork1',
                                   fork2 := fork2'
                          }

/--
We instantiate the state transition class so that we can use some fancy
notation.
-/
-- Aya: StateTransition is a class that has two fields: (1) init of type State and (2) step of type State -> List Event -> State
instance : StateTransition (Event 2) Fork_2_State where
  init := default
  step := step_2_fork

instance : StateTransition (Event 3) Fork_3_State where
  init := default
  step := step_3_fork

instance : StateTransition (Event 3) DoubleForkState where
  init := default
  step := step_double_fork

/--
This theorem states that if we assume that the input_queue has a token with
value 5, then we can read 5 from the 2nd port of fork2 (the third port of the
whole system).  To "execute" the system, we have to manually apply the steps of
the transition system to go from the input step to some output state from which
we can observe a read of the value 5.
-/
theorem can_reach_some_output :
  -- Aya: there exists a state of structure DoubleForkState where the input queue of the fork1 field of the structure contains 1 token of value 5
  -- Aya: and this triggers an event where we can read a token of value 5 from the 2nd port and the Event is of type Event 3
  ∃ s', { (default : DoubleForkState) with fork1.input_queue := [5] }
          -[ [(Event.read_port 2 5 : Event 3)] ]*> s' := by  -- Aya: I'm guessing that this is implication but it happens after "star" events?
    simp [default]; constructor  -- Aya: I guess this refers to the constructor of the StateTransition class...
    -- Aya: The apply tactic only does one thing and that is to change the goal from Q to P, given the hypothesis that P implies Q
    apply step_internal -- Aya: theorem defined in the StateTransition.lean file
    · apply step_double_fork.run_internal_fork1  -- run_internal_fork1 is defined above in the inductive step_double_fork
      apply step_2_fork.internal_step
      and_intros <;> rfl
    · apply step_internal
      · apply step_double_fork.push_internal_token
        apply step_2_fork.handle_read_event
        · unfold enq_Fin; simp
          and_intros <;> rfl
        · apply step_2_fork.handle_write_event
      · apply step_internal
        · apply step_double_fork.run_internal_fork2
          apply step_2_fork.internal_step
          simp; and_intros <;> rfl
        · apply step_one
          apply step_double_fork.handle_read_event2
          · omega
          · have h : subtract_Fin 2 = 1 := by simp [subtract_Fin]
            simp; rw [h]
            apply step_2_fork.handle_read_event
            simp [enq_Fin]; rfl

-- Aya: defining the PHI which represents the relatedness between the states of two systems
inductive φ (two_f_two : DoubleForkState) (one_f_three : Fork_3_State) : Prop where
  -- Aya: I guess this compares two outputs of the two doubleforks with only two outputs of the single three output fork
  -- Not sure what is the syntax for accessing a particular queue in the list of output_queues? For now, I concatenated the two double forks
  | intro : two_f_two.fork1.output_queues 1 ++ two_f_two.fork2.output_queues 2 = one_f_three.output_queues 3 ->  φ two_f_two one_f_three


-- Aya's attempt to prove that DoubleForkState refines Fork_3_State
theorem refinement_proof (two_f_two two_f_two' : DoubleForkState) (one_f_three : Fork_3_State) (events : List (Event 3) ) :
  -- Aya: had an error with star step_double_fork two_f_two l two_f_two' -> ∃ one_f_three', star step_3_fork one_f_three l one_f_three'??
  -- Aya: not sure if we need star_extend that was used in the clock example instead of star?
  φ two_f_two one_f_three -> star two_f_two events two_f_two' -> ∃ one_f_three', star one_f_three events one_f_three' ∧ φ two_f_two' one_f_three' := by
    intro h1 h2  -- extracting two hypothesis from the goal

    revert h1 one_f_three -- it adjusts the goal to saying that for every one_f_three state, if this state is φ related to the two_f_two, then it is possible to do star number of transitions to arrive at a new one_f_three' state that is related to two_f_two l two_f_two'

    induction h2 <;> intro one_f_three  -- break the goal into smaller goals: one for each constructor of star
    -- refl constructor of star
    . intro h2
      exact ⟨ one_f_three, star.refl one_f_three, h2 ⟩
    -- step constructor of star
    . rename_i new_events _ another_new_events new_two_f_two another_new_two_f_two one_step another_step h
      intro h3
      --clear h3  -- seems like this hypothesis does not help so clear it out...
      have h4 := one_step
      have h5 := another_step

      --revert h4 h5 two_f_two

      -- exact ⟨ one_f_three, star.state one_f_three one_f_three' new_events another_new_events , h3 ⟩

      -- (1) how to apply transitivity to say another_new_two_f_two - [ new_events ] *> new_two_f_two?

      -- (2) how to extract parts of h? E.g., it states the φ new_two_f_two one_f_three' which is part of the goal we are trying to prove?

      -- at this point the goal to prove is: there exists one_f_three' such that it comes from a concatenation of new_events and another_new_events and it is PHI related to new_two_f_two (some other doubleForkState)

      -- have new_h := can_reach_some_output
      -- cases new_h

end DataflowRewriter
