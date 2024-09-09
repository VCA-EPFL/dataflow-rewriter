import DataflowRewriter.Module
import Batteries

open Batteries (RBMap)

namespace DataflowRewriter

@[simp]
def io (T : Type) : Module (List T) :=
  { inputs := Std.HashMap.ofList [("inp", ⟨ T, λ s t s' => s' = t :: s ⟩)],
    internals := [],
    outputs := Std.HashMap.ofList [("out", ⟨ T, λ s t s' => s = s' ++ [t] ⟩)]
  }

@[simp]
def merge_inputs (mod : Module S) (in1 in2 : Ident) : Option (Module S)  := do
  let in1_t ← mod.inputs[in1]?;
  let in2_t ← mod.inputs[in2]?;
  let rmin2 := mod.inputs.erase in2;
  some { inputs :=
         rmin2.insert in2 ⟨ in1_t.1 × in2_t.1, λ s (v1,v2) s' =>
               ∃ s_int, in1_t.2 s v1 s_int ∧
               in2_t.2 s_int v2 s'⟩,
         outputs := mod.outputs,
         internals := mod.internals }

@[simp]
def merge_outputs (mod : Module S) (out1 out2 : Ident) : Option (Module S)  := do
  let out1_t ← mod.outputs[out1]?;
  let out2_t ← mod.outputs[out2]?;
  let rmout2 := mod.outputs.erase out2;
      some { outputs :=
               rmout2.insert out2 ⟨ out1_t.1 × out2_t.1, λ s (v1,v2) s' =>
                   ∃ s_int, out1_t.2 s v1 s_int ∧
                   out2_t.2 s_int v2 s' ⟩,
             inputs := mod.inputs,
             internals := mod.internals }

@[simp]
def merge T : Module (List T) :=
      { inputs := Std.HashMap.ofList [("a", ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩),
                   ("b", ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩)],
        outputs := Std.HashMap.ofList [("z", ⟨ T, λ oldList oldElement newList => 
                           ∃ i, newList = oldList.remove i 
                             ∧ oldElement = oldList.get i ⟩)],
        internals := []
      }

@[simp]
def fork T : Module (List T) :=
      { inputs := Std.HashMap.ofList [("a", ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩)],
        outputs := Std.HashMap.ofList [ ("z", ⟨ T, λ oldList oldElement newList => ∃ i, newList = oldList.remove i ∧ oldElement = oldList.get i ⟩)
                   , ("y", ⟨ T, λ oldList oldElement newList => ∃ i, newList = oldList.remove i ∧ oldElement = oldList.get i ⟩)
                   ],
        internals := []
      }

end DataflowRewriter
