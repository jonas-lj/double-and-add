import DoubleAndAdd

open Aeneas Aeneas.Std Result

namespace double_and_add

variable {T : Type} [AddMonoid T]

/-- The Rust `Zero` instance implements the additive monoid structure on `T`: `zero` returns `0`
and `add` returns the sum, and neither fails. -/
structure ImplementsAddMonoid (zeroInst : num_traits.identities.Zero T) : Prop where
  zero_ok : zeroInst.zero = ok 0
  add_ok : ∀ a b, zeroInst.coreopsarithAddInst.add a b = ok (a + b)

end double_and_add
