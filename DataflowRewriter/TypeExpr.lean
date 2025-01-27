/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Lean
import DataflowRewriter.ExprHigh

open Std.Internal (Parsec)
open Std.Internal.Parsec String
open Batteries (AssocList)

namespace DataflowRewriter

inductive TypeExpr where
| nat
| bool
| unit
| pair (left right : TypeExpr)
deriving Repr, DecidableEq

def TypeExpr.denote : TypeExpr → Type
| nat => Nat
| bool => Bool
| unit => Unit
| pair t1 t2 => t1.denote × t2.denote

inductive ValExpr where
| nat (n : Nat)
| bool (b : Bool)
| unit
| pair (left right : ValExpr)
deriving Repr, DecidableEq

def ValExpr.type : ValExpr → TypeExpr
| nat _ => .nat
| bool _ => .bool
| unit => .unit
| pair l r => .pair l.type r.type

def ValExpr.denote : (t : ValExpr) → t.type.denote
| nat n => n
| bool b => b
| unit => ()
| pair t1 t2 => (t1.denote, t2.denote)

inductive FuncName where
| getelementptr_op
| zext_op
| fmul_op
| fadd_op
| add_op
| icmp_ult_op
| mc_store_op
| mc_load_op
| ret_op

inductive FuncExpr where
| typ (t : TypeExpr)
| val (v : ValExpr)
| var
| left (f : FuncExpr)
| right (f : FuncExpr)
| app (n : FuncName) (n : FuncExpr)

namespace TypeExpr.Parser

@[inline] def skipStringWs (s : String) := skipString s <* ws

def parseTypeExpr' (n : Nat) : Parser TypeExpr :=
  match n with
  | n+1 =>
    skipStringWs "Nat" *> pure .nat
    <|> skipStringWs "Bool" *> pure .bool
    <|> skipStringWs "Unit" *> pure .unit
    <|> (do skipStringWs "("
            let t ← parseTypeExpr' n
            skipStringWs "×"
            let t' ← parseTypeExpr' n
            skipStringWs ")"
            return .pair t t'
        )
  | _ => failure

def parseTypeExpr (s : String): Option TypeExpr :=
  match parseTypeExpr' s.length |>.run s with
  | .ok r => .some r
  | .error _ => .none

def parseType (s : String): Option Type :=
  parseTypeExpr s |>.map TypeExpr.denote

end TypeExpr.Parser
end DataflowRewriter
