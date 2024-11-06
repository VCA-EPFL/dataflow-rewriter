/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Lean
import DataflowRewriter.ExprHigh

open Std.Internal (Parsec)
open Std.Internal.Parsec String
open Batteries (AssocList)

namespace DataflowRewriter
namespace Parser

structure DotAttr where
  key : String
  value : String
deriving Inhabited, Repr

structure DotGraph where
  nodes : List (String × List DotAttr)
  edges : List (String × String × List DotAttr)
deriving Inhabited, Repr

instance : EmptyCollection DotGraph := ⟨∅, ∅⟩

def hexChar : Parser Nat := do
  let c ← any
  if '0' <= c && c <= '9' then
    pure $ (c.val - '0'.val).toNat
  else if 'a' <= c && c <= 'f' then
    pure $ (c.val - 'a'.val + 10).toNat
  else if 'A' <= c && c <= 'F' then
    pure $ (c.val - 'A'.val + 10).toNat
  else
    fail "invalid hex character"

def escapedChar : Parser Char := do
  let c ← any
  match c with
  | '\\' => return '\\'
  | '"'  => return '"'
  | '/'  => return '/'
  | 'b'  => return '\x08'
  | 'f'  => return '\x0c'
  | 'n'  => return '\n'
  | 'r'  => return '\x0d'
  | 't'  => return '\t'
  | 'u'  =>
    let u1 ← hexChar; let u2 ← hexChar; let u3 ← hexChar; let u4 ← hexChar
    return Char.ofNat $ 4096*u1 + 256*u2 + 16*u3 + u4
  | _ => fail "illegal \\u escape"

partial def strCore (acc : String) : Parser String := do
  let c ← peek!
  if c == '"' then -- "
    skip
    return acc
  else
    let c ← any
    if c == '\\' then
      strCore (acc.push (← escapedChar))
    -- as to whether c.val > 0xffff should be split up and encoded with multiple \u,
    -- the JSON standard is not definite: both directly printing the character
    -- and encoding it with multiple \u is allowed. we choose the former.
    else if 0x0020 <= c.val && c.val <= 0x10ffff then
      strCore (acc.push c)
    else
      fail "unexpected character in string"

@[inline]
def lookahead (p : Char → Prop) (desc : String) [DecidablePred p] : Parser Unit := do
  let c ← peek!
  if p c then
    return ()
  else
    fail <| "expected " ++ desc

@[inline] def str : Parser String := do
  lookahead (fun c => c == '"') "\""; skip; -- "
  strCore ""

@[inline] def strWs : Parser String := str <* ws

def strDigits : Parser String := do
  let l ← Lean.Json.Parser.num
  return toString l

def strDigitsWs : Parser String := strDigits <* ws

@[inline]
def nonNumericIdentifier : Parser Char := attempt do
  let c ← any
  if ('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z') ∨ (c = '_') ∨ ('\u0200' ≤ c ∧ c ≤ '\u0377')
  then return c else fail s!"ASCII letter expected"

def identifier : Parser String := do
  let c ← nonNumericIdentifier
  let cs ← manyChars (nonNumericIdentifier <|> digit)
  return c.toString ++ cs

def identifierWs := identifier <* ws

def parseId := identifierWs <|> strWs <|> strDigitsWs

def skipStringWs (s : String) := skipString s <* ws
def pstringWs (s : String) := pstring s <* ws
def digitsWs := digits <* ws

def around {α} (delimL delimR : String) (p : Parser α) : Parser α := do
  skipStringWs delimL
  let l ← p
  skipStringWs delimR
  return l

def braces {α} : Parser α → Parser α := around "{" "}"
def brackets {α} : Parser α → Parser α := around "[" "]"
def parens {α} : Parser α → Parser α := around "(" ")"

def delimited' {α} (delim : String) (p : Parser α) : Parser (Array α) := do
  let l ← p
  let l' ← many (attempt <| skipStringWs delim *> p)
    <* (skipStringWs delim <|> ws)
  return (#[l] ++ l')

def delimited {α} (delim : String) (p : Parser α) : Parser (Array α) :=
  delimited' delim p <|> pure #[]

def tryP {α} (p : Parser α) : Parser (Option α) :=
  (some <$> p) <|> pure none

def tryD {α} (a : α) (p : Parser α) : Parser α :=
  p <|> pure a

def parseBool : Parser Bool :=
  (skipString "true" *> pure true)
  <|> (skipString "false" *> pure false)

def parseAttr : Parser DotAttr := do
  let i ← parseId
  skipStringWs "="
  let i' ← parseId
  return ⟨i, i'⟩

def parseNode : Parser (String × List DotAttr) := do
  let i ← parseId
  let l ← tryD #[] <| brackets <| delimited "," parseAttr
  return (i, l.toList)

def parseNodeDG : Parser DotGraph := do
  let n ← parseNode
  return {nodes := [n], edges := []}

def parseEdge : Parser (String × String × List DotAttr) := do
  let i ← parseId
  skipStringWs "->"
  let i' ← parseId
  let l ← tryD #[] <| brackets <| delimited "," parseAttr
  return (i, i', l.toList)

def parseEdgeDG : Parser DotGraph := do
  let n ← parseEdge
  return {nodes := [], edges := [n]}

def combine (a b : DotGraph) : DotGraph :=
  {nodes := a.nodes ++ b.nodes, edges := a.edges ++ b.edges}

def parseComment : Parser Unit :=
  optional (skipString "//" *> many (satisfy (λ c => c ≠ '\n' && c ≠ '\r'))) *> ws

mutual

partial def parseStmnt : Parser DotGraph :=
  attempt (parseEdgeDG <* skipChar ';')
  <|> attempt (parseNodeDG <* skipChar ';')
  <|> attempt (parseAttr *> pure {nodes := [], edges := []} <* skipChar ';')
  <|> parseSubgraph

partial def parseDotGraph : Parser DotGraph := do
  let l ← many (optional parseComment *> parseStmnt <* ws)
  return l.foldl combine ∅

partial def parseSubgraph : Parser DotGraph := do
  skipStringWs "subgraph" *> tryD "defaultId" parseId *> braces parseDotGraph <* ws

end

def parseDigraph := skipStringWs "digraph" <|> skipStringWs "Digraph"

def dotGraph : Parser DotGraph := do
  ws *> parseDigraph *> optional parseId *> braces parseDotGraph <* eof

end Parser

def keyStartsWith (l : List Parser.DotAttr) key val :=
  (l.find? (·.key = key) |>.map (·.value) |>.getD "" |>.startsWith val)

def keyArgNumbers (l : List Parser.DotAttr) key :=
  (l.find? (·.key = key) |>.map (·.value) |>.getD "" |>.splitOn |>.length)

def dotToExprHigh (d : Parser.DotGraph) : Except String (ExprHigh String × AssocList String String) := do
  let mut maps : InstMaps := ⟨ ∅, ∅ ⟩
  let (maps', assoc, _) ← d.nodes.foldlM (λ (a, assoc, arr) (s, l) => do
      let some typ := l.find? (·.key = "type")
        | throw "could not find instance type"
      let mut typVal := typ.value
      let mut arr' := arr
      let mut assoc' := assoc
      if typVal = "Branch" && keyStartsWith l "in" "in1:0" then
        typVal := "BranchC"
      if typVal = "Fork" && keyArgNumbers l "in" > 2 then
        let num := keyArgNumbers l "in"
        typVal := s!"Fork{num}"
      if typVal = "Constant" then
        let some val := l.find? (·.key = "value")
          | throw "could not find \"value\" field in Constant"
        match assoc.find? val.value with
        | some v =>
          typVal := s!"Constant{v}"
        | none =>
          match arr with
          | x :: xs =>
            assoc' := assoc.cons val.value x
            arr' := xs
            typVal := s!"Constant{x}"
          | [] => throw "too many constants"
      if typVal = "Operator" then
        let some op := l.find? (·.key = "op")
          | throw "could not find \"op\" field in Operation"
        match op with
        | _ => typVal := "Add"
      let cluster := l.find? (·.key = "cluster") |>.getD ⟨"cluster", "false"⟩
      let .ok clusterB := Parser.parseBool.run cluster.value
        | throw "cluster could not be parsed"
      let upd ← updateNodeMaps a s typVal clusterB
      return (upd, assoc', arr')
    ) (maps, ∅, ["A", "B", "C", "D", "E", "F", "G"])
  maps := maps'
  let (maps', conns) ← d.edges.foldlM (λ a (s1, s2, l) => do
      let inp := l.find? (·.key = "to")
      let out := l.find? (·.key = "from")
      match updateConnMaps a.fst a.snd s1 s2 (out.map (·.value)) (inp.map (·.value)) with
      | .ok v => return v
      | .error s => throw s.toString
    ) (maps, [])
  return (⟨ maps'.instTypeMap.toList.toAssocList, conns ⟩, assoc)

end DataflowRewriter

open DataflowRewriter in
def String.toExprHigh (s : String) : Except String (ExprHigh String × AssocList String String) := do
  let l ← Parser.dotGraph.run s
  dotToExprHigh l
