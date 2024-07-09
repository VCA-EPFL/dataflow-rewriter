import Lake
open Lake DSL

require «leanses» from git "https://github.com/VCA-EPFL/leanses" @ "main"
require batteries from git "https://github.com/leanprover-community/batteries" @ "main"

package «dataflow-rewriter» where
  -- add package configuration options here

lean_lib «DataflowRewriter» where
  -- add library configuration options here

@[default_target]
lean_exe «dataflow-rewriter» where
  root := `Main
