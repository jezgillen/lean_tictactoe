import Lake
open Lake DSL

package «tictactoe» where
  -- add package configuration options here

lean_lib «Tictactoe» where
  -- add library configuration options here

@[default_target]
lean_exe «tictactoe» where
  root := `Main
