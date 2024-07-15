import Lake
open Lake DSL

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "8ba988d4920812778905a15253a188a588ad5783"

package «dataflow-rewriter» where
  -- add package configuration options here

lean_lib «DataflowRewriter» where
  -- add library configuration options here

@[default_target]
lean_exe «dataflow-rewriter» where
  root := `Main
