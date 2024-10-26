/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Lean

open Std.Internal (Parsec)
open Std.Internal.Parsec String

namespace DataflowRewriter.Parser

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
  let l ← digits
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

def parseStmnt : Parser DotGraph :=
  attempt parseEdgeDG <|> parseNodeDG

def combine (a b : DotGraph) : DotGraph :=
  {nodes := a.nodes ++ b.nodes, edges := a.edges ++ b.edges}

def parseDotGraph : Parser DotGraph := do
  let l ← delimited ";" parseStmnt
  return l.foldl combine ∅

def dotGraph : Parser DotGraph := do
  ws *> skipStringWs "digraph" *> braces parseDotGraph <* eof

#eval dotGraph.run "digraph { hello [ar=23];   hello2[ar=28]  ; 123 ->3 ; hello; }"

end DataflowRewriter.Parser
