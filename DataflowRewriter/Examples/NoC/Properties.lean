import Lean
import Init.Data.BitVec.Lemmas
import Qq

import DataflowRewriter.Simp
import DataflowRewriter.Module
import DataflowRewriter.ExprLow
import DataflowRewriter.ExprLowLemmas
import DataflowRewriter.Component
import DataflowRewriter.KernelRefl
import DataflowRewriter.Reduce
import DataflowRewriter.List
import DataflowRewriter.Tactic
import DataflowRewriter.AssocList

import DataflowRewriter.Examples.NoC.Basic
import DataflowRewriter.Examples.NoC.Components

open Batteries (AssocList)

namespace DataflowRewriter.NoC

-- Basic properties of the NoC component ---------------------------------------

theorem noc_inpT (i : RouterID) :
  i < P.netsz → (noc.inputs.getIO ↑i).1 = (P.Data × FlitHeader) :=
  by
    intros Hle
    unfold noc lift_f
    dsimp
    rw [PortMap.getIO_map (i := i) (f := mk_noc_input_rule) (Heq := by unfold mk_noc_input_rule; rfl)]
    <;> simpa

theorem noc_outT (i : RouterID) :
  i < P.netsz →
  (noc.outputs.getIO i).1 = P.Data :=
  by
    intros Hle
    unfold noc lift_f
    dsimp
    rw [PortMap.getIO_map (i := i) (f := mk_noc_output_rule) (Heq := by unfold mk_noc_output_rule; rfl)]
    <;> simpa

-- TODO: We can prove something stronger, where we can do other rule than
-- internal rules.
-- We can create an inductive which is a subset of existsSR of all rules (need
-- to prove id), and then show that we can use this inductive to get to any
-- internal step
theorem full_connectivity (i j : RouterID) (d : P.Data) pre_s inp_s
  (iLt : i < P.netsz) (jLt : j < P.netsz):
  -- From any initial state `in_s`, if we can add a message from input port `i`
  -- with destination port `j` containing data `d`, changing the state to
  -- `mid_s`...
  (noc.inputs.getIO i).2 pre_s ((noc_inpT i iLt).mpr (d, { dest := j })) inp_s →
  -- Then there exists an internal execution path from this `mid_s` to an output
  -- state `out_s`
  -- NOTE: We know that noc.internals is actually empty in our current
  -- definition, but we don't want to expose this fact to users
  ∃ mid_s, existSR noc.internals inp_s mid_s ∧
  -- This `out_s` can be used to extract the initial data `d`
  ∃ out_s, (noc.outputs.getIO j).2 mid_s ((noc_outT j jLt).mpr d) out_s
  := by
    intros Hinp
    unfold noc at *
    dsimp at *
    exists inp_s
    split_ands
    · constructor
    · let inp_i := mk_noc_input_rule i
      rw [PortMap.rw_rule_execution
        (h := by
          apply (PortMap.getIO_map (i := i) (f := mk_noc_input_rule) (Heq := by
            unfold mk_noc_input_rule; rfl))
          <;> simpa)
      ] at Hinp
      · exists pre_s
        let out_j := mk_noc_output_rule j
        rw [PortMap.rw_rule_execution
          (h := by
            apply (PortMap.getIO_map (i := j) (f := mk_noc_output_rule) (Heq := by
              unfold mk_noc_output_rule; rfl))
            <;> simpa)
        ]
        dsimp
        dsimp at Hinp
        have Hlen: 0 < List.length inp_s
        · simpa [Hinp]
        exists (Fin.mk 0 Hlen)
        split_ands <;> simpa [Hinp]
