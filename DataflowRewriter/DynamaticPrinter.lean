/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.Rewriter


open Batteries (AssocList)

namespace DataflowRewriter

/--
This should ideally be linked and generated from the environment definition in
the Component.lean file.

- It is also not clear what the type for tagged components should be.
- TODO Check that the IO names correspond to the implementation.
-/
def interfaceTypes (m : AssocList String String) :=
  [
     ("Merge", (some "Merge", "in1:32 in2:32", "out1:32", []))
     -- TODO: figure out how to distinguish phi_c from phi because they should have different delays
     -- Aya: Follow Yann's way of differentiating the internal types of Branch vs. BranchC
   , ("mux T", (some "mux T", "in1?:1 in2:32 in3:32", "out1:32", [("delay", "0.366")]))

    -- Aya: Given our current loop rewrites, I do not think we will need a Cmerge
   --, ("CntrlMerge", (some "CntrlMerge", "in1:32 in2:32", "out1:32 out2?:1", [("delay", "0.366")]))

    -- assuming that any fork can only be 2-input
   , ("fork Bool 2", (some "fork Bool 2", "in1:32", "out1:32 out2:32", []))

   , ("Entry", (some "Entry", "in1:0", "out1:0", [("control", "true")]))

   , ("init Bool false", (some "init Bool false", "in1:32 in2:32", "out1:32", []))

   , ("branch T", (some "branch T", "in1:32 in2?:1", "out1+:32 out2-:32", []))

   , ("Sink", (some "Sink", "in1:32", "", []))

  ].toAssocList


def removeLetter (ch : Char) (s : String) : String :=
  String.mk (s.toList.filter (λ c => c ≠ ch))

def returnNatInstring (s : String) : Option Nat :=
  -- Convert the string to a list of characters
  let chars := s.toList
  let result := List.foldl (λ acc c =>
      if c.isDigit then
        acc * 10 + (Char.toNat c - Char.toNat '0')
      else
        acc) 0 chars
  -- If no non-digit character was encountered, return the result
  -- if result = 0 then
  --   if s.isEmpty then some 0 else none
  -- else
  some result

def incrementDefinitionPortIdx (s direction: String) : String :=
  -- Split the string by spaces into individual parts (like "out0:32")
  let parts := s.splitOn " "
  -- Map over each part, incrementing the number after "out"
  let updatedParts := parts.map (λ part =>
    match part.splitOn ":" with
    | [pref, num] =>
      match (returnNatInstring pref) with
      | some n =>
        -- Increment the number found
        let incremented := n + 1
        -- Reconstruct the string with the incremented number
        direction ++ Nat.repr incremented ++ ":" ++ (num)
      | none => part -- If no number is found, keep the part unchanged
    | _ => part -- If the part doesn't have ":" or a valid number, keep it unchanged
  )
  -- Join the updated parts into a single string with spaces
  String.intercalate " " updatedParts

#eval incrementDefinitionPortIdx "out1:32" "out"  --out1:324 out2:32 out3:32" "out"  -- Output: "out1:32 out4:32 out3:32"

#eval "out132".splitOn ":"

def incrementConnectionPortIdx (s direction: String) : String :=
   match returnNatInstring s with
  | some n =>
    let incremented := n + 1
    -- Convert incremented number to a string and concatenate with the direction part
    let incrementedStr := Nat.repr incremented
    direction ++ incrementedStr
  | none => s  -- If no number is found, return the original string

#eval incrementConnectionPortIdx "out33" "out"

-- Function became messy...
def formatOptions : List (String × String) → String
| x :: l => l.foldl
    (λ s (sl, sr) =>
      let v1 := if sl = "in" then removeLetter 'p' sr else sr
      let v1_ := if sl = "bbID" || sl = "bbcount" || sl = "ldcount" || sl = "stcount" then s!"{v1}" else s!"\"{v1}\""
      s ++ s!", {sl} = {v1_}")
    (let v2 := if x.1 = "in" then (removeLetter 'p' x.2) else x.2
     let v2_ := if x.1= "bbID" ||  x.1 = "bbcount" ||  x.1 = "ldcount" ||  x.1 = "stcount" then s!"{v2}" else s!"\"{v2}\""
     s!", {x.1} = {v2_}")
| [] => ""

def extractStandardType (s : String) : String :=
  let parts := s.splitOn " "
  parts.get! 0

def capitalizeFirstChar (s : String) : String :=
  match s.get? 0 with
  | none   => s  -- If the string is empty, return it as is
  | some c =>
    let newChar := if 'a' ≤ c ∧ c ≤ 'z' then
                     Char.ofNat (c.toNat - ('a'.toNat - 'A'.toNat))
                   else
                     c
    newChar.toString ++ s.drop 1

def CharToInt(c : Char) : Nat :=
   if c.isDigit then
    Char.toNat c - Char.toNat '0'  -- Subtract the Unicode value of '0' to get the integer value
  else
    0  -- Return 0 if the character is not a digit (you could handle this differently)

-- Aya: Add a functions to add a constant and trigger it from start then feed it to the Merge
def InitToMerge (s : String) : String :=
  if s = "Init" then
    "Merge"
  else
    s  -- Otherwise, return the original string


--fmt.1: Type
--fmt.2.1 and fmt.2.2.1: Input and output attributes
--fmt.2.2.2: Additional options.
def dynamaticString (a: ExprHigh String) (m : AssocList String (AssocList String String)): Option String := do
  -- let instances :=
  --   a.modules.foldl (λ s inst mod => s ++ s!"\n {inst} [mod = \"{mod}\"];") ""
  let a ← a.normaliseNames
  let modules ←
    a.modules.foldlM
      (λ s k v => do
        let fmt := (interfaceTypes ∅).find? v.snd |>.getD (some v.snd, "", "", [("unsupported", "true")])
        match m.find? k with
        | some input_fmt =>
          -- TODO: If the node is of type Init, add a new constant node to later connect to the 2nd input of the Merge that'll implement the Init
          let constForInit := ""
          -- If we find that the node comes from the input, but just add the input arguments to it that we saved.
          return s ++ constForInit ++ s!"  {k} [type = \"{InitToMerge (capitalizeFirstChar (extractStandardType (fmt.1.getD v.snd)))}\"{formatOptions input_fmt.toList}];\n"
        | none =>
          -- If this is a new node, then we sue `fmt` to correctly add the right
          -- arguments.  We should never be generating constructs like MC, so
          -- this shouldn't be a problem.
          return s ++ s!"  {k} [type = \"{InitToMerge (capitalizeFirstChar (extractStandardType (fmt.1.getD v.snd)))}\", in = \"{removeLetter 'p' fmt.2.1}\", out = \" {fmt.2.2.1} \"{formatOptions fmt.2.2.2}];\n"
        ) ""
  let connections :=
    a.connections.foldl
      (λ s => λ | ⟨ oport, iport ⟩ =>
                  s ++ s!"\n  {oport.inst} -> {iport.inst} "
                    ++ s!"[from = \"{oport.name}\","
                    ++ s!" to = \"{removeLetter 'p' iport.name}\" "
                    ++ "];") ""
  s!"digraph \{
{modules}
{connections}
}"

end DataflowRewriter
