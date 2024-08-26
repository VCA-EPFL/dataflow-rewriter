import Leanses
import Lean
import Init.Data.BitVec.Lemmas
import Mathlib
import Qq

import DataflowRewriter.Simp
import DataflowRewriter.Module

open Qq

open Batteries (AssocList)
open Batteries (RBMap)

open Lean.Meta Lean.Elab

example : True :
