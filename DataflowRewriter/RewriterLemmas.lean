/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.ExprHighLemmas
import DataflowRewriter.Rewriter

open Batteries (AssocList)

namespace DataflowRewriter

section Refinement

universe v w

variable (ε : IdentMap String ((T : Type _) × Module String T))

theorem EStateM.bind_eq_ok {ε σ α β} {x : EStateM ε σ α} {f : α → EStateM ε σ β} {s v s'} :
  x.bind f s = .ok v s' →
  ∃ (x_int : α) (s_int : σ),
    x s = .ok x_int s_int ∧ f x_int s_int = .ok v s' := by
  unfold EStateM.bind; split <;> tauto

theorem ofOption_eq_ok {ε σ α} {e : ε} {o : Option α} {o' : α} {s s' : σ} :
  ofOption e o s = EStateM.Result.ok o' s' →
  o = o' ∧ s = s' := by
  unfold ofOption
  split <;> (intros h; cases h)
  constructor <;> rfl

theorem liftError_eq_ok {σ α} {o : Except String α} {o' : α} {s s' : σ} :
  liftError o s = EStateM.Result.ok o' s' →
  o = .ok o' ∧ s = s' := by
  unfold liftError; split <;> (intros h; cases h)
  constructor <;> rfl

theorem guard_eq_ok {ε σ} (e : ε) (b : Bool) {o' : Unit} {s s' : σ} :
  EStateM.guard e b s = EStateM.Result.ok o' s' →
  b = true ∧ s = s' := by
  unfold EStateM.guard; split <;> (intros h; cases h)
  subst b; constructor <;> rfl

theorem Rewrite_run'_correct {g g' : ExprHigh String} {s rw _st _st'} :
  Rewrite.run' s g rw _st = .ok g' _st' →
  ([Ge| g', ε ]) ⊑ ([Ge| g, ε ]) := by
  unfold Rewrite.run'; simp; intro hrewrite
  dsimp [Bind.bind, Monad.toBind, EStateM.instMonad] at *
  repeat
    rename (EStateM.bind _ _ _ = .ok _ _) => hrewrite
    replace hrewrite := EStateM.bind_eq_ok hrewrite
    let ⟨_, _, _, hrewrite'⟩ := hrewrite
    clear hrewrite; have hrewrite := hrewrite'; clear hrewrite'
  repeat
    try have hofOption' := hofOption; clear hofOption
    rename (ofOption _ _ _ = .ok _ _) => hofOption
    replace hofOption := ofOption_eq_ok hofOption
    cases hofOption
  repeat
    try have hofOption' := hofOption; clear hofOption
    rename (liftError _ _ = .ok _ _) => hofOption
    replace hofOption := liftError_eq_ok hofOption
    cases hofOption
  repeat
    try have hofOption' := hofOption; clear hofOption
    rename (guard _ _ _ = .ok _ _) => hofOption
    replace hofOption := guard_eq_ok hofOption
    cases hofOption
  subst_vars


  -- unfold EStateM.bind ofOption at *
  -- repeat (dsimp -failIfUnchanged at *; split at hrewrite <;> try injection hrewrite)
  -- set_option pp.explicit true in trace_state


theorem Rewrite_abstraction_correct {g g' : ExprHigh String} {s a c} :
  Abstraction.run s g a = .ok (g', c) →
  ([Ge| g', ε ]) ⊑ ([Ge| g, ε ]) := by sorry

theorem Rewrite_concretisation_correct {g g' : ExprHigh String} {s c} :
  Concretisation.run s g c = .ok g' →
  ([Ge| g', ε ]) ⊑ ([Ge| g, ε ]) := by sorry

theorem Rewrite_run_correct {g g' : ExprHigh String} {s rw} :
  Rewrite.run s g rw = .ok g' →
  ([Ge| g', ε ]) ⊑ ([Ge| g, ε ]) := by sorry

theorem rewrite_loop_correct {g g' : ExprHigh String} {s rws n} :
  rewrite_loop s g rws n = .ok g' →
  ([Ge| g', ε ]) ⊑ ([Ge| g, ε ]) := by sorry

end Refinement

end DataflowRewriter
