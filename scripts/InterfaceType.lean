module
public import Lean

open Lean

/-- Serialize a declaration's elaborated type in a separately imported environment.
This local equality check is supporting evidence, not a Comparator receipt. -/
public def main (args : List String) : IO UInt32 := do
  let [modName, declName] := args | return 2
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := modName.toName }] {} (level := .private)
  let some ci := env.find? declName.toName | return 3
  IO.println (reprStr ci.type)
  return 0
