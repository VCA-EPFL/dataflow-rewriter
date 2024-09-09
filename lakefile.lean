import Lake
open Lake DSL

require «leanses» from git "https://github.com/VCA-EPFL/leanses" @ "main"
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "2eb00cae7edccf4e54238db2cb4b0a7dff59fbdd"

package «dataflow-rewriter» where
  -- add package configuration options here

@[default_target]
lean_lib «DataflowRewriter» where
  -- add library configuration options here

lean_exe «dataflow-rewriter» where
  root := `Main
