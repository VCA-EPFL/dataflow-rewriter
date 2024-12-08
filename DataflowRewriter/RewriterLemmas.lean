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

theorem Rewrite_run'_correct {g g' : ExprHigh String} {s rw} :
  Rewrite.run' s g rw = .ok g' →
  ([Ge| g', ε ]) ⊑ ([Ge| g, ε ]) := by
  unfold Rewrite.run'; simp; intro hrewrite
  dsimp [Bind.bind, Monad.toBind, Except.instMonad, Except.bind] at *
  repeat (split at hrewrite <;> try injection hrewrite)

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
