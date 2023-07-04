import Lake
open Lake DSL

-- Configuration file copied from NNG4.
-- See: https://github.com/hhu-adam/NNG4

def LocalGameServer : Dependency := {
  name := `GameServer
  src := Source.path "../lean4game/server"
}

def RemoteGameServer : Dependency := {
  name := `GameServer
  src := Source.git "https://github.com/leanprover-community/lean4game.git" "main" "server"
}

-- Choose dependency depending on the environment variable `NODE_ENV`.
open Lean in
#eval (do
  let gameServerName :=
    if (← IO.getEnv "NODE_ENV") == some "development" then ``LocalGameServer else ``RemoteGameServer
  modifyEnv (fun env => Lake.packageDepAttr.ext.addEntry env gameServerName)
    : Elab.Command.CommandElabM Unit)

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

package filtergame {}

@[default_target]
lean_lib FilterGame {}
