import DoubleAndAddSpec

/-!
Checks that the main theorems depend only on the allowed axioms. A `sorry` shows up as the axiom
`sorryAx`, and any `axiom` declaration as itself, so both make this file fail to compile. CI runs
it with `lake env lean CheckAxioms.lean`.
-/

open Lean Elab Command

/-- The axioms the proofs may depend on: Lean's standard axioms. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- `#check_axioms foo` fails if `foo` depends on an axiom that is not in `allowedAxioms`. -/
elab "#check_axioms " thm:ident : command => do
  let constName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo thm
  let axs ← liftCoreM <| collectAxioms constName
  let disallowed := axs.filter (· ∉ allowedAxioms)
  if disallowed.isEmpty then
    logInfo m!"'{constName}' depends only on allowed axioms: {axs}"
  else
    logError m!"'{constName}' depends on disallowed axioms: {disallowed}"

#check_axioms double_and_add.double_and_add_spec
