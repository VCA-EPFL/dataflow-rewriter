/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.ExprHigh

open Std.Internal (Parsec)
open Std.Internal.Parsec String

namespace DataflowRewriter

inductive JSLang where
| join : String → JSLang → JSLang → JSLang
| split1 : String → JSLang → JSLang
| split2 : String → JSLang → JSLang
| I : JSLang
deriving DecidableEq, Repr

def toSExpr : JSLang → String
| .join s l1 l2 =>
  s!"(join \"{s}\" {toSExpr l1} {toSExpr l2})"
| .split1 s l =>
  s!"(split1 \"{s}\" {toSExpr l})"
| .split2 s l =>
  s!"(split2 \"{s}\" {toSExpr l})"
| .I => "I"

def JSLang.construct (term : Nat) (succ : Std.HashMap String (Array (String × String × String))) (startN endN port : String) : Option JSLang :=
  if startN = endN then pure .I else
  match term with
  | 0 => .none
  | term'+1 =>
    match succ[startN]?.map (·.toList) with
    | .some [a, b] => do -- join node
      let jsA ← construct term' succ a.1 endN a.2.2
      let jsB ← construct term' succ b.1 endN b.2.2
      return .join startN jsA jsB
    | .some [a] => do -- split node
      let js ← construct term' succ a.1 endN a.2.2
      if port == "out0" then
        return split1 startN js
      else
        return split2 startN js
    | _ => .none -- error

inductive JSLangRewrite where
| assocL (s1 s2 : String)
| assocR (s1 s2 : String)
| comm (s : String)
| elim (s : String)

def parseRewrites (s : String) : Except String (List JSLangRewrite) := do
  match ← Lean.Json.parse s with
  | .arr a =>
    a.foldrM (λ jObj l => do
        let rw ← jObj.getObjVal? "rw"
        let args ← jObj.getObjVal? "args"
        match rw with
        | "L" =>
          let arg0 ← args.getArrVal? 0 >>= Lean.Json.getStr?
          let arg1 ← args.getArrVal? 1 >>= Lean.Json.getStr?
          return JSLangRewrite.assocL arg0 arg1 :: l
        | "R" =>
          let arg0 ← args.getArrVal? 0 >>= Lean.Json.getStr?
          let arg1 ← args.getArrVal? 1 >>= Lean.Json.getStr?
          return JSLangRewrite.assocR arg0 arg1 :: l
        | "E" =>
          let arg0 ← args.getArrVal? 0 >>= Lean.Json.getStr?
          return JSLangRewrite.elim arg0 :: l
        | "C" =>
          let arg0 ← args.getArrVal? 0 >>= Lean.Json.getStr?
          return JSLangRewrite.comm arg0 :: l
        | _ => throw "Rewrite not recognised"
      ) []
  | _ => throw "Top-level JSON object is not an array"

end DataflowRewriter
