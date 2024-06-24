import Lake
open Lake DSL

package «dataflow-rewriter» where
  -- add package configuration options here

lean_lib «DataflowRewriter» where
  -- add library configuration options here

@[default_target]
lean_exe «dataflow-rewriter» where
  root := `Main
