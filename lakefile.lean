import Lake
open Lake DSL


package «F_system» where
  -- add package configuration options here

lean_lib «FSystem» where
  -- add library configuration options here
@[default_target]
lean_exe «f_system» where
  root := `Main
