import DoubleAndAddEquiv

/-!
Correctness of the Aeneas translation, derived from the equivalence with the hand-written
translation in `DoubleAndAddEquiv.lean` and the correctness of the hand-written translation in
`DoubleAndAddTranslation.lean`.
-/

open Aeneas Aeneas.Std Result

namespace double_and_add

variable {T : Type} [AddMonoid T]

/-- Correctness of double-and-add: for any type whose `Zero` instance implements an additive
monoid, `double_and_add base n` succeeds and returns `n • base`. -/
theorem double_and_add_spec (zeroInst : num_traits.identities.Zero T)
    (copyInst : core.marker.Copy T) (h : ImplementsAddMonoid zeroInst) (base : T) (n : U64) :
    double_and_add zeroInst copyInst base n = ok (n.val • base) := by
  rw [double_and_add_eq_doubleAndAdd zeroInst copyInst h,
    DoubleAndAddTranslation.doubleAndAdd_spec]

end double_and_add
