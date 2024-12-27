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
def OldinterfaceTypes (m : AssocList String String) :=
  [ ("Join", (none, "in1:32 in2:32", "out1:64", []))
  , ("TaggedJoin", (none, "in1:32 in2:32", "out1:64", []))

  , ("Split", (none, "in1:64", "out1:32 out2:32", []))
  , ("TaggedSplit", (none, "in1:64", "out1:32 out2:32", []))

  , ("Merge", (none, "in1:32 in2:32", "out1:32", []))
  , ("TagggedMerge", (none, "in1:32 in2:32", "out1:32", []))

  , ("Fork", (none, "in1:32", "out1:32 out2:32", []))
  , ("Fork3", (some "Fork", "in1:32", "out1:32 out2:32 out3:32", []))
  , ("Fork4", (some "Fork", "in1:32", "out1:32 out2:32 out3:32 out4:32", []))
  , ("Fork5", (some "Fork", "in1:32", "out1:32 out2:32 out3:32 out4:32 out5:32", []))
  , ("Fork6", (some "Fork", "in1:32", "out1:32 out2:32 out3:32 out4:32 out5:32 out6:32", []))
  , ("TagggedFork", (none, "in1:32", "out1:32 out2:32", []))

  -- TODO FIX DELAY
  , ("CntrlMerge", (none, "in1:32 in2:32", "out1:32 out2?:1", [("delay", "1.234510"), ("delay2", "1.234510")]))
  , ("TagggedCntrlMerge", (none, "in1:32 in2:32", "out1:32 out2?:1", []))

  , ("Branch", (some "Branch", "in1:32 in2?:1", "out1+:32 out2-:32", []))
 , ("BranchC", (some "Branch", "in1:0 in2?:1", "out1+:0 out2-:0", []))
 , ("TagggedBranch", (none, "in1:32 in2?:1", "out1+:32 out2-:32", []))

  , ("Mux", (none, "in1?:1 in2:32 in3:32", "out1:32", []))
  , ("MuxC", (some "Mux", "in1?:1 in2:0 in3:0", "out1:0", []))

  , ("TagggedMux", (none, "in1?:1 in2:32 in3:32", "out1:32", []))
  , ("Buffer", (none, "in1:32", "out1:32", []))
  , ("BufferC", (some "Buffer", "in1:0", "out1:0", []))
  , ("BufferB", (some "Buffer", "in1:1", "out1:1", []))
  , ("TagggedBuffer", (none, "in1:32", "out1:32", []))

  -- Should not appear in output
  , ("Bag", (none, "in1:32", "out1:32", []))

  -- Does not quite match the current formalisation, where you only output one
  -- value.  Maybe the formalisation needs to add a split to the end.
  , ("Aligner", (none, "in1:32 in2:32", "out1:32 out2:32", []))
  , ("TaggerCntrlAligner", (none, "in1:32 in2:32", "out1:32 out2:32", []))

  , ("Sink", (none, "in1:32", "", []))

  -- Constants are currently axiomatised
  , ("ConstantA", (some "Constant", "in1:0", "out1:32", [("value", m.find? "A" |>.getD "unrecognised")]))
  , ("ConstantB", (some "Constant", "in1:0", "out1:32", [("value", m.find? "B" |>.getD "unrecognised")]))
  , ("ConstantC", (some "Constant", "in1:0", "out1:32", [("value", m.find? "C" |>.getD "unrecognised")]))
  , ("ConstantD", (some "Constant", "in1:0", "out1:32", [("value", m.find? "D" |>.getD "unrecognised")]))
  , ("ConstantE", (some "Constant", "in1:0", "out1:32", [("value", m.find? "E" |>.getD "unrecognised")]))
  , ("ConstantF", (some "Constant", "in1:0", "out1:32", [("value", m.find? "F" |>.getD "unrecognised")]))
  , ("ConstantG", (some "Constant", "in1:0", "out1:32", [("value", m.find? "G" |>.getD "unrecognised")]))

  -- Operations are also axiomatised
  , ("Add", (some "Operator", "in1:32 in2:32", "out1:32", [("op", "add")]))
  , ("Mul", (some "Operator", "in1:32 in2:32", "out1:32", [("op", "mul")]))
  , ("Div", (some "Operator", "in1:32 in2:32", "out1:32", [("op", "div")]))
  , ("Shl", (some "Operator", "in1:32 in2:32", "out1:32", [("op", "shl")]))
  , ("Sub", (some "Operator", "in1:32 in2:32", "out1:32", [("op", "sub")]))
  ].toAssocList

def interfaceTypes (m : AssocList String String) :=
  [
     ("Merge", (some "Merge", "in1:32 in2:32", "out1:32", []))
     -- TODO: figure out how to distinguish phi_c from phi because they should have different delays
   , ("mux T", (some "mux T", "in1?:1 in2:32 in3:32", "out1:32", [("delay", "0.366")]))

    -- Aya: Given our current loop rewrites, I do not think we will need a Cmerge
   --, ("CntrlMerge", (some "CntrlMerge", "in1:32 in2:32", "out1:32 out2?:1", [("delay", "0.366")]))

    -- assuming that any fork can only be 2-input
   , ("fork Bool 2", (some "fork Bool 2", "in1:32", "out1:32 out2:32", []))

   , ("Entry", (some "Entry", "in1:0", "out1:0", [("control", "true")]))

   , ("init Bool false", (some "init Bool false", "in1:32 in2:32", "out1:32", []))

   , ("branch T", (some "branch T", "in1:32 in2?:1", "out1+:32 out2-:32", []))

   , ("Sink", (some "Sink", "in1:32", "", []))

    -- Constants are currently axiomatised
   , ("ConstantA", (some "Constant", "in1:0", "out1:32", [("value", m.find? "A" |>.getD "unrecognised")]))
   , ("ConstantB", (some "Constant", "in1:0", "out1:32", [("value", m.find? "B" |>.getD "unrecognised")]))
   , ("ConstantC", (some "Constant", "in1:0", "out1:32", [("value", m.find? "C" |>.getD "unrecognised")]))
   , ("ConstantD", (some "Constant", "in1:0", "out1:32", [("value", m.find? "D" |>.getD "unrecognised")]))
   , ("ConstantE", (some "Constant", "in1:0", "out1:32", [("value", m.find? "E" |>.getD "unrecognised")]))
   , ("ConstantF", (some "Constant", "in1:0", "out1:32", [("value", m.find? "F" |>.getD "unrecognised")]))
   , ("ConstantG", (some "Constant", "in1:0", "out1:32", [("value", m.find? "G" |>.getD "unrecognised")]))

  -- Operations are also axiomatised
   , ("OperatorA", (some "Operator", "in1:32 in2:32", "out1:32", [("op", m.find? "add_op" |>.getD "unrecognised")]))
   , ("OperatorB", (some "Operator", "in1:32 in2:32", "out1:32", [("op", m.find? "fadd_op" |>.getD "unrecognised")]))
   , ("OperatorC", (some "Operator", "in1:32 in2:32", "out1:32", [("op", m.find? "fmul_op" |>.getD "unrecognised")]))
   , ("OperatorD", (some "Operator", "in1:32", "out1:32", [("op", m.find? "zext_op" |>.getD "unrecognised")]))
   , ("OperatorE", (some "Operator", "in1:32 in2:32", "out1:1", [("op", m.find? "icmp_ult_op" |>.getD "unrecognised")]))

   , ("OperatorF", (some "Operator", "in1:32 in2:32 in3:32", "out1:32", [("op", m.find? "getelementptr_op" |>.getD "unrecognised")]))

   , ("OperatorG", (some "Operator", "in1:32 in2:32", "out1:32", [("op", m.find? "mc_load_op" |>.getD "unrecognised")]))
   , ("OperatorH", (some "Operator", "in1:32 in2:32", "out1:32", [("op", m.find? "mc_store_op" |>.getD "unrecognised")]))

   , ("OperatorI", (some "Operator", "in1:32", "out1:32", [("op", m.find? "ret_op" |>.getD "unrecognised")]))

   , ("MC", (some "MC", "in1:0", "out1:32", []))


  ].toAssocList

def formatOptions : List (String × String) → String
| x :: l => l.foldl (λ s (sl, sr) => s ++ s!", {sl} = \"{sr}\"") s!", {x.1} = \"{x.2}\""
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

-- Function to extract the first multi-digit number from a string, add 1, and return the modified string
def addOneToFirstNumber (s : String) : String :=
  let digits := s.toList  -- Convert the string to a list of characters
  -- Extract the first sequence of digits from the string
  let (numList, rest) := digits.span (λ c => c.isDigit)  -- Extract the digits of the number
  match numList.toString.toNat? with
  | some n =>
    let newNumber := n + 1  -- Add 1 to the extracted number
    let newNumberStr := toString newNumber  -- Convert the updated number back to a string
    let pref := s.take (s.length - rest.length - numList.length)  -- Take part of the string before the number
    let suff := s.drop (s.length - rest.length)  -- Take part of the string after the number
    pref ++ newNumberStr ++ suff  -- Combine them to form the modified string
  | none => s  -- If no number is found, return the original string

def removeLetter (ch : Char) (s : String) : String :=
  String.mk (s.toList.filter (λ c => c ≠ ch))

def renameInit (s : String) : String :=
  if s = "Init" then
    "Merge"
  else
    s  -- Otherwise, return the original string

def dynamaticString (a: ExprHigh String) (m : AssocList String String): Option String := do
  -- let instances :=
  --   a.modules.foldl (λ s inst mod => s ++ s!"\n {inst} [mod = \"{mod}\"];") ""
  let a ← a.normaliseNames
  let modules ←
    a.modules.foldlM
      (λ s k v => do
        let fmt := (interfaceTypes m).find? v.snd |>.getD (some v.snd, "", "", [("unsupported", "true")])
        return s ++ s!"  {k} [type = \"{renameInit (capitalizeFirstChar (extractStandardType (fmt.1.getD v.snd)))}\", in = \"{fmt.2.1}\", out = \"{fmt.2.2.1}\"{formatOptions fmt.2.2.2}];\n"
        ) ""
  let connections :=
    a.connections.foldl
      (λ s => λ | ⟨ oport, iport ⟩ =>
                  s ++ s!"\n  {oport.inst} -> {iport.inst} "
                    ++ s!"[from = \"{addOneToFirstNumber oport.name}\","
                    ++ s!" to = \"{removeLetter 'p' (addOneToFirstNumber iport.name)}\" "
                    ++ "];") ""
  s!"digraph \{
{modules}
{connections}
}"

-- TODO: The addOneToFirstNumber is not working as expected as it does not add 1 :(

end DataflowRewriter
