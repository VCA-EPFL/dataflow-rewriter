/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.Module
import DataflowRewriter.Simp
import DataflowRewriter.ExprHigh
import DataflowRewriter.AssocList.Basic
import DataflowRewriter.TypeExpr
import DataflowRewriter.Environment

open Batteries (AssocList)

namespace DataflowRewriter.CombModule

def Stream α := Int → α

namespace Stream

def empty {α} [Inhabited α] : Stream α := fun _ => default

instance {α} [Inhabited α] : Inhabited (Stream α) := ⟨empty⟩

def map {α β} (f : α → β) (s : Stream α) : Stream β := fun n => f (s n)

end Stream

-- We thought we needed a top and bot value for streams, essentially operating on 4-valued logic.  However, we do not
-- need a top-value, because we don't have to signal any errors when two streams do not agree.  Instead, we block the
-- execution of the module if the streams do not agree.
-- For the same reason, we also do not need a bot value, because if we cannot define the result at some point, then we
-- can also block.
-- Also, I think we need integers instead of natural numbers for the domain, so that you have all the future and the
-- past values that you will ever get.  If you end up caring only about the past values, then maybe you can use naturals
-- again.
abbrev D := Stream Bool

def merge_streams (s1 s2 : D) : Prop := ∀ i, s1 i = s2 i

def delay (s : D) : D | n => s (n-1)

def s_not (s : D) : D := s.map (!·)

def not : NatModule D :=
  { inputs := [(0, ⟨ D, λ s tt s' => merge_streams s tt ∧ s' = s_not (delay tt) ⟩)].toAssocList,
    outputs := [(0, ⟨ D, λ s tt s' => s = s' ∧ s = tt⟩)].toAssocList
    init_state := λ s => s = default
  }

end DataflowRewriter.CombModule
