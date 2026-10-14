import Common
import DoubleAndAdd

/-!
Specs of the functions in `src/lib.rs`, proved directly on the Aeneas translation in
`DoubleAndAdd.lean`. `CheckAxioms.lean` checks that every theorem here depends only on the allowed
axioms.

Each theorem's doc comment states the spec in ordinary mathematical terms, independently of the
Lean syntax. The two must say the same thing.

Conventions used in the doc comments:
* `(T, +, 0)` is an additive monoid: `+` is associative and `0` is a left and right identity. `+`
  need not be commutative.
* For `n ∈ ℕ` and `b ∈ T`, `n · b = b + b + ⋯ + b` with `n` terms, and `0 · b = 0`.
* A Rust function *returns `v`* if it terminates without panicking, overflowing or failing an
  assertion, and its result is `v`. In Lean, this is `f … = ok v`.
-/

open Aeneas Aeneas.Std Result

namespace double_and_add

variable {T : Type} [AddMonoid T]

/-- **Assumption on the Rust trait implementations.**

The Rust `Zero` implementation for `T`, including its supertrait `Add`, computes the monoid
operations of `(T, +, 0)`:
* `T::zero()` returns `0`, and
* `Add::add(a, b)` returns `a + b` for all `a, b ∈ T`.

The specs below assume this; it has to be proved separately for each concrete type `T`. -/
class ImplementsAddMonoid (zeroInst : num_traits.identities.Zero T) : Prop where
  zero_ok : zeroInst.zero = ok 0
  add_ok : ∀ a b, zeroInst.coreopsarithAddInst.add a b = ok (a + b)

variable {zeroInst : num_traits.identities.Zero T} {copyInst : core.marker.Copy T}

/-- **Correctness of `double_and_add`.**

Let `(T, +, 0)` be an additive monoid whose Rust `Zero` and `Add` implementations compute `0` and
`+` (`ImplementsAddMonoid`). Then for all `b ∈ T` and all `n ∈ {0, …, 2⁶⁴ − 1}`,
`double_and_add(b, n)` returns

  `n · b = b + b + ⋯ + b`  (`n` terms; `0` if `n = 0`). -/
theorem double_and_add_spec [ImplementsAddMonoid zeroInst] (base : T) (n : U64) :
    double_and_add zeroInst copyInst base n = ok (n.val • base) := by
  induction hk : n.val using Nat.strong_induction_on generalizing n with
  | _ k ih =>
  unfold double_and_add
  split_ifs with h0
  · subst h0; subst hk; simp [ImplementsAddMonoid.zero_ok]
  · have hn : n.val ≠ 0 := fun e => h0 (UScalar.eq_of_val_eq e)
    obtain ⟨m, hm, hmv⟩ := WP.spec_imp_exists (U64.div_spec n (y := 2#u64) (by decide))
    obtain ⟨r, hr, hrv⟩ := WP.spec_imp_exists (U64.rem_spec n (y := 2#u64) (by decide))
    simp at hmv hrv
    have hlt : m.val < k := by omega
    simp [hm, hr, ih m.val hlt m rfl, ImplementsAddMonoid.add_ok]
    split_ifs with hodd
    · rw [← add_nsmul, ← succ_nsmul]; congr 2
      have := congrArg UScalar.val hodd; simp at this; omega
    · rw [← add_nsmul]; congr 2
      have : r.val ≠ 1 := fun e => hodd (UScalar.eq_of_val_eq (by simpa using e))
      omega

end double_and_add
