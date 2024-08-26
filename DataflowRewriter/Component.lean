-- @[simp]
-- def source (l : List ((T : Type) × T)) : Module (Fin l.length → ((T : Type) × List T)) :=
--   { inputs := ((List.drange l.length).zip l).map
--               (λ (n, (Sigma.mk T d)) => ⟨ T, λ s t s' => s' = update_Fin n ⟩),
--     internals := [],
--     outputs := l.map (λ (Sigma.mk T d) => ⟨ T, λ _ t _ => t = d ⟩)
--   }

@[simp]
def io (T : Type) : Module (List T) :=
  { inputs := [⟨ T, λ s t s' => s' = t :: s ⟩],
    internals := [],
    outputs := [⟨ T, λ s t s' => s = s' ++ [t] ⟩]
  }

@[simp]
def sink (l : List Type) : Module Unit :=
  { inputs := l.map (λ T => ⟨ T, λ _ _ _ => True ⟩),
    internals := [],
    outputs := []
  }

@[simp]
def merge_inputs (mod : Module S) (in1 in2 : Fin (List.length mod.inputs)) : Module S  :=
      { inputs :=
        let in1_t := mod.inputs.get in1;
        let in2_t := mod.inputs.get in2;
        let rmin2 := List.remove mod.inputs in2;
        List.set rmin2 in2.1 ⟨ in1_t.1 × in2_t.1, λ s (v1,v2) s' =>
              ∃ s_int, in1_t.2 s v1 s_int ∧
              in2_t.2 s_int v2 s'⟩
      ,
        outputs := mod.outputs,
        internals := mod.internals }
@[simp]
def merge_outputs (mod : Module S) (out1 out2 : Fin (List.length mod.outputs)) : Module S  :=
      { outputs :=
        let out1_t := mod.outputs.get out1;
        let out2_t := mod.outputs.get out2;
        let rmout2 := List.remove mod.outputs out2;
        List.set rmout2 out2.1 ⟨ out1_t.1 × out2_t.1, λ s (v1,v2) s' =>
              ∃ s_int, out1_t.2 s v1 s_int ∧
              out2_t.2 s_int v2 s'⟩
      ,
        inputs := mod.inputs,
        internals := mod.internals }

@[simp]
def merge T : Module (List T):=
      { inputs := [⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩,
                   ⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩],
        outputs := [⟨ T, λ oldList oldElement newList => ∃ i, newList = oldList.remove i ∧ oldElement = oldList.get i ⟩],
        internals := []
      }

@[simp]
def fork T : Module (List T):=
      { inputs := [⟨ T, λ oldList newElement newList => newList = newElement :: oldList ⟩],
        outputs := [ ⟨ T, λ oldList oldElement newList => ∃ i, newList = oldList.remove i ∧ oldElement = oldList.get i ⟩
                   , ⟨ T, λ oldList oldElement newList => ∃ i, newList = oldList.remove i ∧ oldElement = oldList.get i ⟩
                   ],
        internals := []
      }
