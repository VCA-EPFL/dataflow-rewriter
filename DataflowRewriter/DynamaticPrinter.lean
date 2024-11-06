/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.Rewriter
import DataflowRewriter.ExprHighElaborator

open Batteries (AssocList)

namespace DataflowRewriter

/--
This should ideally be linked and generated from the environment definition in
the Component.lean file.

- It is also not clear what the type for tagged components should be.
- TODO Check that the IO names correspond to the implementation.
-/
def interfaceTypes (m : AssocList String String) :=
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

  , ("Branch", (none, "in1:32 in2?:1", "out1+:32 out2-:32", []))
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

  -- TODO WRONG
  , ("Sink", (none, "in1:32 in2:32", "out1:32 out2:32", []))

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

def formatOptions : List (String × String) → String
| x :: l => l.foldl (λ s (sl, sr) => s ++ s!", {sl} = \"{sr}\"") s!", {x.1} = \"{x.2}\""
| [] => ""

def dynamaticString (a: ExprHigh String) (m : AssocList String String): Option String := do
  -- let instances :=
  --   a.modules.foldl (λ s inst mod => s ++ s!"\n {inst} [mod = \"{mod}\"];") ""
  let a ← a.normaliseNames
  let (io_decl, io_conn) := a.modules.foldl (λ (sdecl, sio) inst (pmap, typ) =>
    let sdecl := (pmap.input ++ pmap.output).foldl (λ sdecl k v =>
      if v.inst.isTop
      then sdecl ++ s!"\n  {v.name} [type = \"io\", label = \"{v.name}: io\"];"
      else sdecl) sdecl
    let sio := pmap.input.foldl (λ io_conn k v =>
      if v.inst.isTop
      then io_conn ++ s!"\n  {v.name} -> {inst} [to = \"{k.name}\", headlabel = \"{k.name}\"];"
      else io_conn) sio
    let sio := pmap.output.foldl (λ io_conn k v =>
      if v.inst.isTop
      then io_conn ++ s!"\n  {inst} -> {v.name} [from = \"{k.name}\", taillabel = \"{k.name}\"];"
      else io_conn) sio
    (sdecl, sio)
  ) ("", "")
  let modules ←
    a.modules.foldlM
      (λ s k v => do
        let fmt := (interfaceTypes m).find? v.snd |>.getD (some v.snd, "", "", [("unsupported", "true")])
        return s ++ s!"  {k} [type = \"{fmt.1.getD v.snd}\", label = \"{k}: {v.snd}\", in = \"{fmt.2.1}\", out = \"{fmt.2.2.1}\"{formatOptions fmt.2.2.2}];\n"
        ) ""
  let connections :=
    a.connections.foldl
      (λ s => λ | ⟨ oport, iport ⟩ =>
                  s ++ s!"\n  {oport.inst} -> {iport.inst} "
                    ++ s!"[from = \"{oport.name}\","
                    ++ s!" to = \"{iport.name}\","
                    ++ s!" taillabel = \"{oport.name}\","
                    ++ s!" headlabel = \"{iport.name}\","
                    ++ "];") ""
  s!"digraph \{
{io_decl}
{modules}
{io_conn}
{connections}
}"

end DataflowRewriter
