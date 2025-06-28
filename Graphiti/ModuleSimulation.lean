/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Lean
import Qq

import Graphiti.Module

open Batteries (AssocList)

namespace Graphiti

/-- Input function --/
@[simp] abbrev FunIn (S : Type _) := Σ T : Type, S → T → Option S

/-- Output function --/
@[simp] abbrev FunOut (S : Type _) := Σ T : Type, S → Option (T × S)

/-- Internal function --/
@[simp] abbrev FunInt (S : Type _) := S → Option S

structure SModule (Ident S : Type _) where
  inputs : PortMap Ident (FunIn S)
  outputs : PortMap Ident (FunOut S)
  internals : List (FunInt S) := []
  init_state : S
deriving Inhabited

namespace SModule

variable {Ident S : Type _}

def FunIn.toRelIO (f : FunIn S) : RelIO S :=
  ⟨f.1, fun s t s' => f.2 s t = some s'⟩

def FunOut.toRelIO (f : FunOut S) : RelIO S :=
  ⟨f.1, fun s t s' => f.2 s = some (t, s')⟩

def FunInt.toRelInt (f : FunInt S) : RelInt S :=
  fun s s' => f s = some s'

-- def toModule (sm : SModule Ident S) : Module Ident S :=
--   { inputs := sm.inputs.mapVal (λ _ v => v.toRelIO),
--     outputs := sm.outputs.mapVal (λ _ v => v.toRelIO),
--     internals := sm.internals.map FunInt.toRelInt,
--     init_state := λ s => s = sm.init_state,
--   }

-- def

end SModule

end Graphiti
