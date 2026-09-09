import DR
import Lean.Util.CollectAxioms

/-! Audit every project declaration, including private helper declarations. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (name, _) in env.constants.toList do
    let label := name.toString
    if label.startsWith "DittertRybin." || label.startsWith "_private.DR." then
      checked := checked + 1
      for ax in ← collectAxioms name do
        unless allowed.contains ax do
          logError m!"Unexpected axiom dependency: {name} -> {ax}"
  if checked == 0 then
    logError "The project axiom audit matched no declarations."
  logInfo m!"Audited {checked} project declarations."
