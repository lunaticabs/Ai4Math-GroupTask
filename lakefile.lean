import Lake
open Lake DSL

package «lambda» where
  -- add package configuration options here

lean_lib «Lambda» where
  -- add library configuration options here

@[default_target]
lean_exe «lambda» where
  root := `Main
