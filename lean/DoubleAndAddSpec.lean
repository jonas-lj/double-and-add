import DoubleAndAdd

open Aeneas Aeneas.Std Result

namespace double_and_add

variable {T : Type} [AddMonoid T]

/-- The Rust `Zero` and `Clone` instances behave like the additive monoid structure on `T`:
`zero` returns `0`, `add` returns the sum, and `clone` returns its argument, and none of them
fail. -/
structure IsAddMonoid (zeroInst : num_traits.identities.Zero T)
    (cloneInst : core.clone.Clone T) : Prop where
  zero_ok : zeroInst.zero = ok 0
  add_ok : ∀ a b, zeroInst.coreopsarithAddInst.add a b = ok (a + b)
  clone_ok : ∀ a, cloneInst.clone a = ok a

/-- Shifting a `u64` right by one never fails and halves its value. -/
theorem shr_one (n : U64) : ∃ m : U64, n >>> 1#i32 = ok m ∧ m.val = n.val / 2 := by
  obtain ⟨m, hm, hv, -⟩ :=
    WP.spec_imp_exists (U64.ShiftRight_IScalar_spec n 1#i32 (by decide) (by decide))
  exact ⟨m, hm, by rw [hv, Nat.shiftRight_eq_div_pow]; rfl⟩

/-- Correctness of double-and-add: for any type whose `Zero` and `Clone` instances behave like an
additive monoid, `double_and_add base n` succeeds and returns `n • base`. -/
theorem double_and_add_spec (zeroInst : num_traits.identities.Zero T)
    (cloneInst : core.clone.Clone T) (h : IsAddMonoid zeroInst cloneInst) (base : T) (n : U64) :
    double_and_add zeroInst cloneInst base n = ok (n.val • base) := by
  induction hk : n.val using Nat.strong_induction_on generalizing n with
  | _ k ih =>
  unfold double_and_add
  split
  · subst hk; rw [h.zero_ok, show (0#64#uscalar : U64).val = 0 from rfl, zero_nsmul]
  · rename_i hne
    obtain ⟨m, hm, hmv⟩ := shr_one n
    have hn : n.val ≠ 0 := fun h0 => hne (UScalar.eq_of_val_eq h0)
    have hlt : m.val < k := by omega
    simp [hm, ih m.val hlt m rfl, h.clone_ok, h.add_ok, lift]
    have hodd : n &&& 1#u64 = 1#u64 ↔ n.val % 2 = 1 := by
      rw [← Nat.and_one_is_mod]
      constructor
      · intro e
        simpa [UScalar.val_and] using congrArg UScalar.val e
      · intro e
        apply UScalar.eq_of_val_eq
        simpa [UScalar.val_and] using e
    split_ifs with hbit
    · rw [hodd] at hbit
      rw [← add_nsmul, ← succ_nsmul]
      congr 2
      omega
    · rw [hodd] at hbit
      rw [← add_nsmul]
      congr 2
      omega

end double_and_add
