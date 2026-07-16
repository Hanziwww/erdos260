import Erdos260

open Lean

/-! Print every non-internal declaration in the `Erdos260` namespace, one per line. -/
unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Erdos260 }] {}
  for (name, _) in env.constants.toList do
    if (`Erdos260).isPrefixOf name && !name.isInternal then
      IO.println name
