import DataflowRewriter.StateTransition
import Lean
import Mathlib.Tactic

open Lean Meta Elab

namespace DataflowRewriter

/--
This is the main state of a fork that produces 2 outputs, it consists of the input and output queues,
which are just lists of tokens (natural numbers).
-/
structure Fork_2_State where
  input_queue : Queue
  output_queues : Fin 2 → Queue  -- List of 2 Lists
  deriving Inhabited, Repr  -- Autogenerates a default structure that can serve for intializiation
/--

-/
structure Fork_3_State where
  input_queue : Queue
  output_queues : Fin 3 → Queue  -- List of 3 Lists: has the syntax of a function
  deriving Inhabited, Repr

/--
We now construct a state for the larger system, which combines the 2 2-output forks
into the greater fork, which should then be equivalent with a fork with 3
outputs.

Here we can reuse the fork states of the forks themselves, so that in the
semantics we can reuse the semantics of a single fork.
-/
structure DoubleForkState where
  -- 2 instances of the above Fork_2_State
  fork1 : Fork_2_State
  fork2 : Fork_2_State
  deriving Inhabited, Repr


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
-- Models a transition from one fork state to another through a list of Events where each event has two output queues
inductive step_2_fork : Fork_2_State → List (Event 2) → Fork_2_State → Prop where
  -- has three constructors which we can think of as firing rules each resulting in the transition from one state to another

  -- A write event means the concatenation of a token at the input queue
  | handle_write_event : ∀ s v,  -- for any state s and token v, if there is a write event that is passed a token v,
    -- concatenate (++) that token to the end of the input_queue
    step_2_fork s [Event.write_port v] { s with input_queue := s.input_queue ++ [v] }

  -- A read event means the removal of a token from the output queue
  | handle_read_event : ∀ s n v rst,
    -- if the output queue has a token v at the top of the queue (:: is opposite of ++). All of the output queues are modeled as "rst"
    -- this serves as a precondition (guard) for the occurrence of a read event (i.e., firing rule) and it requires a token at the output queue at index n
    s.output_queues n = v :: rst →
    -- call the update_Fin function that takes the index n, the token v, the queue rst before the token v and returns the output queues after adding v to the specific queue indexed at n
    step_2_fork s [Event.read_port n v] { s with output_queues := update_Fin n rst s.output_queues }

  -- An internal step signals the propagation of a token from the input queue to be added to the output queue
  -- This firing rule should then make the handle_read_event rule applicable
  | internal_step : ∀ s v rst,
    -- if the input queue has a token v at the top of the queue (:: is opposite of ++). The input queue is modeled as "rst"
    -- this serves as a precondition (guard) for the occurrence of an internal event (i.e., firing rule). Note that this does not trigger any output events (that is why the list of events below is empty)
    s.input_queue = v :: rst →
    -- call the enq_Fin function that takes an index determining which output queue to write to by conctenating the token v. Here, it is called once to propagate to queue 0 and another time to queue 1. It also removes the token from the input_queue that is why it assigns rst to it
    step_2_fork s [] { s with output_queues := enq_Fin 0 v (enq_Fin 1 v s.output_queues), input_queue := rst }

/--
Models a transition from one fork state to another through a list of Events that have 3 output ports
-/
inductive step_3_fork : Fork_3_State → List (Event 3) → Fork_3_State → Prop where
| handle_write_event : ∀ s v,
    step_3_fork s [Event.write_port v] { s with input_queue := s.input_queue ++ [v] }
| handle_read_event : ∀ s n v rst,
    s.output_queues n = v :: rst →
    step_3_fork s [Event.read_port n v] { s with output_queues := update_Fin n rst s.output_queues }
| internal_step : ∀ s v rst,  -- local variables used by the constructor
    s.input_queue = v :: rst →  -- add an element ot the top of the list of output queues
    step_3_fork s [] { s with output_queues := enq_Fin 0 v (enq_Fin 1 v (enq_Fin 2 v s.output_queues)), input_queue := rst}

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
  -- the guard here requires the trigger of the write_port firing rule of step_2_fork producing fork1'
    step_2_fork s.fork1 [Event.write_port v] fork1' →
  -- triggering this rule results in fork1 of the DoubleForkState structure becoming the fork1'
    step_double_fork s [Event.write_port v] { s with fork1 := fork1' }
/--
Read a token from the external port of fork1 (queue 0 only because queue 1 is internal).
-/
  | handle_read_event1 : ∀ s fork1' v,
   -- the guard here requires the trigger of the read_port firing rule of step_2_fork producing fork1'
    step_2_fork s.fork1 [Event.read_port 0 v] fork1' →
   -- triggering this rule results in fork1 of the DoubleForkState structure becoming the fork1'
    step_double_fork s [Event.read_port 0 v] { s with fork1 := fork1' }
/--
Read a token from the external ports of fork2 (port 1 and 2).
-/
  | handle_read_event2 : ∀ s fork2' (n : Fin 3) v,
  -- the guard here requires the trigger of the read_port firing rule of step_2_fork producing fork2' and additionally requires that the event does not happen on the 0th output queue of the 3 output queues in the structure of DoubleForkState (because this is taken care of by the above rule)
    n ≠ 0 →
    step_2_fork s.fork2 [Event.read_port (subtract_Fin n) v] fork2' →
    step_double_fork s [Event.read_port n v] { s with fork2 := fork2' }
/--
Run an internal step of fork1.
-/
  | run_internal_fork1 : ∀ s fork1',
  -- the guard here requires the trigger of the internal step of step_2_fork which requires no external events that is why []
    step_2_fork s.fork1 [] fork1' →
    step_double_fork s [] { s with fork1 := fork1' }
/--
Run an internal step of fork2.
-/
  | run_internal_fork2 : ∀ s fork2',
  -- the guard here requires the trigger of the internal step of step_2_fork which requires no external events that is why []
    step_2_fork s.fork2 [] fork2' →
    step_double_fork s [] { s with fork2 := fork2' }
/--
Push a token from the port of fork1 to the input port of fork2.
-/
  | push_internal_token : ∀ s v fork1' fork2',
  -- there are two guards promoting for propagation of tokens: (1) read event on fork1 and wrtie event on fork2 and it requires no external events on the global DoubleForkState.. It will then trigger the handle_read_event2
    step_2_fork s.fork1 [Event.read_port 1 v] fork1' →  -- read from output queue 1 of fork1 because output queue 0 is a global output
    step_2_fork s.fork2 [Event.write_port v] fork2' →
    step_double_fork s [] { s with fork1 := fork1',
                                   fork2 := fork2'
                          }

/--
We instantiate the state transition class so that we can use some fancy
notation.
-/
-- StateTransition is a class that has two fields: (1) init of type State and (2) step of type State -> List Event -> State
instance : StateTransition (Event 2) Fork_2_State where
  init := default
  step := step_2_fork

instance : StateTransition (Event 3) Fork_3_State where
  init := default
  step := step_3_fork

instance : StateTransition (Event 3) DoubleForkState where
  init := default
  step := step_double_fork


-- Defining the PHI which represents the relatedness between the states of two systems
inductive φ (two_f_two : DoubleForkState) (one_f_three : Fork_3_State) : Prop where
  | intro :
    two_f_two.fork1.output_queues 0 ++ two_f_two.fork1.input_queue = one_f_three.output_queues 0 ++ one_f_three.input_queue →
    two_f_two.fork2.output_queues 0 ++ two_f_two.fork1.output_queues 1 ++ two_f_two.fork1.input_queue = one_f_three.output_queues 1 ++ one_f_three.input_queue →
    two_f_two.fork2.output_queues 1 ++ two_f_two.fork1.output_queues 1 ++ two_f_two.fork1.input_queue = one_f_three.output_queues 2 ++ one_f_three.input_queue →
    φ two_f_two one_f_three

-- To simplify the ultimate refinement proof, we assume that we do only a single transition from DoubleForkState to another DoubleFork state and we search for a Fork_3_State that comes after a star number of transition from another Fork_3_state and is PHI related to the final DoubleForkState
theorem refinement_proof_simplified (two_f_two two_f_two' : DoubleForkState) (one_f_three : Fork_3_State) (events : List (Event 3) ) :
  φ two_f_two one_f_three → step_double_fork two_f_two events two_f_two' -> ∃ one_f_three', star one_f_three events one_f_three' ∧ φ two_f_two' one_f_three' := by
  intros hphi hstep
  rcases hphi with ⟨ Hi1, Hi2, Hi3 ⟩  -- recusrsivley break down the PHI constructor and rename its different parts with Hi1, Hi2, Hi3

  cases hstep with  -- try out all possibilities for the single step_double_fork
  | handle_write_event fork' v hstep2 =>
    cases hstep2
    constructor
    and_intros
    . apply star.plus_one
      apply step_3_fork.handle_write_event

    . apply φ.intro <;> (simp; repeat rw [← List.append_assoc]) <;> [ rw [Hi1]; rw [Hi2]; rw [Hi3] ]

  | handle_read_event1 fork' v hstep3 =>
    cases hstep3
    constructor
    and_intros
    . apply star.plus_one   -- exclude the star frim step_3_state
      rename_i rst _
      apply step_3_fork.handle_read_event one_f_three 0 v rst -- directly apply the read event
      rename_i two_f_two_applic

      -- I want to say given that step_2_fork has this applicable and given that they are PHI related, this means that the goal is correct????

    . apply φ.intro <;> (simp; repeat rw [← List.append_assoc]) <;> [ rw [Hi1]; rw [Hi2]; rw [Hi3] ]
      -- How to prove that they receive the same input??


  | handle_read_event2 fork' v hstep4 =>
    cases hstep4

  | handle_read_event1 fork' v hstep5 =>
    cases hstep5

  | run_internal_fork1 : fork' hstep6 =>
    cases hstep6

  | run_internal_fork2 : fork' hstep7 =>

  | push_internal_token : fork1' fork2' v hstep8 =>




theorem refinement_proof_full (two_f_two two_f_two' : DoubleForkState) (one_f_three : Fork_3_State) (events : List (Event 3) ) :
  φ two_f_two one_f_three -> star two_f_two events two_f_two' -> ∃ one_f_three', star one_f_three events one_f_three' ∧ φ two_f_two' one_f_three' := by
    intro h1 h2  -- extracting two hypothesis from the goal

    revert h1 one_f_three -- it adjusts the goal to saying that for every one_f_three state, if this state is φ related to the two_f_two, then it is possible to do star number of transitions to arrive at a new one_f_three' state that is related to two_f_two'

    -- the following are just two tactics on one line, that is why we are separating them with <;>
    induction h2  <;> intro one_f_three -- break the goal into smaller goals: one for each constructor of star
    -- refl constructor of star
    . intro h2
      exact ⟨ one_f_three, star.refl one_f_three, h2 ⟩
    -- step constructor of star
    . rename_i new_events i_mid another_new_events new_two_f_two another_new_two_f_two one_step _ h
      intro h3
      have href := refinement_proof_simplified _ _ _ _ h3 one_step

      rcases href with ⟨ s_mid, hrefstep, hrefphi ⟩
      -- Note that the above rcases does recursive cases and can be replaced by the following cases
      -- cases href
      -- rename_i _ s_mid hrefphi
      -- cases hrefphi
      -- rename_i _ _ hrefphi

      have h' := h s_mid hrefphi
      rcases h' with ⟨ s_final, hrefmultstep, hrefmultphi ⟩

      -- the following removes the there exists from the goal because we found out that it truly exists by finding s_final
      exists s_final

      and_intros
      . apply star.trans_star <;> assumption
      . assumption


/--
This theorem states that if we assume that the input_queue has a token with
value 5, then we can read 5 from the 2nd port of fork2 (the third port of the
whole system).  To "execute" the system, we have to manually apply the steps of
the transition system to go from the input step to some output state from which
we can observe a read of the value 5.
-/
-- this theorem can't be used in the refinement proof though because it is very specific to value 5
theorem can_reach_some_output :
  -- There exists a state of structure DoubleForkState where the input queue of the fork1 field of the structure contains 1 token of value 5
  -- This triggers an event where we can read a token of value 5 from the 2nd port and the Event is of type Event 3
  ∃ s', { (default : DoubleForkState) with fork1.input_queue := [5] }
          -[ [(Event.read_port 2 5 : Event 3)] ]*> s' := by
    simp [default]; constructor
    apply step_internal -- apply a theorem defined in StateTransition.lean
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


end DataflowRewriter

-- Aya: not sure of the following:
/--
(1) not fully clear if we only pass the parameters or also some of the hypothesis stated in the theorem (i.e., h3): have href := refinement_proof_simplified _ _ _ _ h3 one_step

-/
