/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Lean

register_simp_attr dmod
register_simp_attr drunfold
register_simp_attr drcompute
register_simp_attr drdecide
register_simp_attr drnat
register_simp_attr drunfold_defs

-- def fromExpr? (e : Expr) : SimpM (Option String) := do
--   return getStringValue? et

open Lean Meta Simp

-- simproc ↓ decideDecidable (Bool.rec _ _ c) := fun e => do
--   let_expr f@Bool.rec _ a b c ← e | return .continue
--   let r ← simp c
--   return .done r

-- @[inline] def reduceBoolPred (declName : Name) (arity : Nat) (op : String → String → Bool) (e : Expr) : SimpM DStep := do
--   unless e.isAppOfArity declName arity do return .continue
--   let some n ← Expr.fromExpr? e.appFn!.appArg! | return .continue
--   let some m ← fromExpr? e.appArg! | return .continue
--   return .done <| toExpr (op n m)


-- structure A where
--   a : String
--   b : String
-- deriving DecidableEq

-- example b : (match ({ a := "", b := "b" } : A) == { a := "", b := "c" } with
--              | true => 1
--              | false => 2) = b := by
--   -- simp
--   have : (({ a := "", b := "b" } : A) == { a := "", b := "c" }) = false := by decide
--   unfold _example.match_1
--   simp [_example.match_1]

--   sorry

def fromExpr? (e : Expr) : SimpM (Option Nat) :=
  getNatValue? e

@[inline] def reduceToStringImp (e : Expr) : SimpM Simp.DStep := do
  let some n ← fromExpr? e.appArg! | return .continue
  return .done <| .lit <| .strVal <| toString n

-- Reduce `toString 5` to `"5"`
dsimproc [simp, seval] reduceToString (toString (_ : Nat)) := reduceToStringImp
