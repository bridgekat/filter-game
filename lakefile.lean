import Lake
open Lake DSL

package «filter4» {
  -- add package configuration options here
}

lean_lib «Filter4» {
  -- add library configuration options here
}

@[default_target]
lean_exe «filter4» {
  root := `Main
}
