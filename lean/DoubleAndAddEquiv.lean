import DoubleAndAddSpec
import DoubleAndAddTranslation

/-!
The Aeneas translation in `DoubleAndAdd.lean` agrees with the hand-written translation in
`DoubleAndAddTranslation.lean`: whenever the Rust `Zero` instance implements an additive monoid,
the Aeneas function succeeds and returns the same value as the hand-written one.

The proof follows the two definitions step by step and never uses what they compute, so it
shows that the hand-written translation is a faithful reading of the Rust code. As a
consequence, correctness of the hand-written translation carries over to the Aeneas one.
-/

open Aeneas Aeneas.Std Result

namespace double_and_add

variable {T : Type} [AddMonoid T]

/-- The Aeneas translation succeeds and agrees with the hand-written translation. -/
theorem double_and_add_eq_doubleAndAdd (zeroInst : num_traits.identities.Zero T)
    (copyInst : core.marker.Copy T) (h : ImplementsAddMonoid zeroInst) (base : T) (n : U64) :
    double_and_add zeroInst copyInst base n =
      ok (DoubleAndAddTranslation.doubleAndAdd base n.val) := by
  induction hk : n.val using Nat.strong_induction_on generalizing n with
  | _ k ih =>
  subst hk
  unfold double_and_add DoubleAndAddTranslation.doubleAndAdd
  dsimp only
  by_cases h0 : n = 0#u64
  · simp [h0, h.zero_ok]
  · have hn : n.val ≠ 0 := fun e => h0 (UScalar.eq_of_val_eq (by simpa using e))
    obtain ⟨m, hm, hmv⟩ := WP.spec_imp_exists (U64.div_spec n (y := 2#u64) (by decide))
    obtain ⟨r, hr, hrv⟩ := WP.spec_imp_exists (U64.rem_spec n (y := 2#u64) (by decide))
    simp at hmv hrv
    have hlt : m.val < n.val := by omega
    have hodd : r = 1#u64 ↔ n.val % 2 = 1 := by
      constructor
      · intro e; have := congrArg UScalar.val e; simp at this; omega
      · intro e; exact UScalar.eq_of_val_eq (by simp; omega)
    have hrec := ih m.val hlt m rfl
    rw [hmv] at hrec
    simp only [h0, hn, if_false, hm, hr, h.add_ok]
    by_cases ho : n.val % 2 = 1
    · simp [hodd.mpr ho, ho, hrec]
    · simp [mt hodd.mp ho, Nat.mod_two_ne_one.mp ho, hrec]

/-- Correctness of the Aeneas translation, derived from correctness of the hand-written one. -/
theorem double_and_add_spec' (zeroInst : num_traits.identities.Zero T)
    (copyInst : core.marker.Copy T) (h : ImplementsAddMonoid zeroInst) (base : T) (n : U64) :
    double_and_add zeroInst copyInst base n = ok (n.val • base) := by
  rw [double_and_add_eq_doubleAndAdd zeroInst copyInst h,
    DoubleAndAddTranslation.doubleAndAdd_spec]

end double_and_add
