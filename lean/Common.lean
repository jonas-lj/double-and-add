import Lean

/-!
Project-wide definitions used by the specs, kept out of the spec files so those contain only
what needs reviewing.
-/

/-! ## Axiom check

Checks that theorems depend only on the allowed axioms. A `sorry` shows up as the axiom `sorryAx`,
and an `axiom` declaration as itself, for example a Rust function that Aeneas could not translate.
-/

open Lean Elab Command

/-- The axioms that proofs may depend on: Lean's standard axioms. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- `#check_axioms_in M` fails if a theorem declared in module `M` depends on an axiom that is not
in `allowedAxioms`. Private and auxiliary theorems are checked through the theorems using them. -/
elab "#check_axioms_in " mod:ident : command => do
  let env ← getEnv
  let some modIdx := env.getModuleIdx? mod.getId
    | throwError "unknown module '{mod.getId}'"
  let theorems := env.constants.map₁.toList.filterMap fun (n, info) =>
    if info matches .thmInfo _ && !n.isInternal && env.getModuleIdxFor? n == some modIdx then
      some n
    else
      none
  if theorems.isEmpty then
    throwError "no theorems found in module '{mod.getId}'"
  for thm in theorems.toArray.qsort Name.lt do
    let axs ← liftCoreM <| collectAxioms thm
    let disallowed := axs.filter (· ∉ allowedAxioms)
    unless disallowed.isEmpty do
      let line := (← liftCoreM <| findDeclarationRanges? thm).map (·.range.pos.line)
      logError m!"'{thm}' ({mod.getId}.lean:{line.getD 0}) depends on disallowed axioms: \
        {disallowed}"
