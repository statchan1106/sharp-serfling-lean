import SharpSerfling
import Lean.Util.CollectAxioms

open Lean Elab Command

/-- Audit every declaration in the project namespace, rather than only a
hand-maintained list of headline theorems.  The command fails if any declaration
depends on an assumption outside Lean's standard logical foundations. -/
elab "#audit_sharp_serfling" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  let mut failures : Array String := #[]
  for (decl, _) in env.constants do
    if decl.toString.startsWith "SharpSerfling" then
      checked := checked + 1
      let axioms ← Lean.collectAxioms decl
      for axiomName in axioms do
        unless allowed.contains axiomName do
          failures := failures.push s!"{decl} depends on {axiomName}"
  unless failures.isEmpty do
    throwError "Full axiom audit failed:\n{String.intercalate "\n" failures.toList}"
  logInfo m!"FULL_AXIOM_AUDIT_OK: checked {checked} SharpSerfling declarations; only propext, Classical.choice, and Quot.sound are used"

#audit_sharp_serfling
