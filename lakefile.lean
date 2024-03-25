import Lake
open Lake DSL

package «LFTCM2024TraceClass» where
  -- add package configuration options here

lean_lib «LFTCM2024TraceClass» where
  -- add library configuration options here

@[default_target]
lean_exe «lftcm2024traceclass» where
  root := `Main

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "1640667583db65dab892533b0059dac5c0a67270"
