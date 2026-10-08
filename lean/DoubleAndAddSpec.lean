import DoubleAndAddAssumptions

open Aeneas Aeneas.Std Result

namespace double_and_add

variable {T : Type} [AddMonoid T]

/-- Correctness of double-and-add: for any type whose `Zero` instance implements an additive
monoid, `double_and_add base n` succeeds and returns `n • base`. -/
theorem double_and_add_spec (zeroInst : num_traits.identities.Zero T)
    (copyInst : core.marker.Copy T) (h : ImplementsAddMonoid zeroInst) (base : T) (n : U64) :
    double_and_add zeroInst copyInst base n = ok (n.val • base) := by
  induction hk : n.val using Nat.strong_induction_on generalizing n with
  | _ k ih =>
  unfold double_and_add
  split_ifs with h0
  · subst h0; subst hk; simp [h.zero_ok]
  · have hn : n.val ≠ 0 := fun e => h0 (UScalar.eq_of_val_eq e)
    obtain ⟨m, hm, hmv⟩ := WP.spec_imp_exists (U64.div_spec n (y := 2#u64) (by decide))
    obtain ⟨r, hr, hrv⟩ := WP.spec_imp_exists (U64.rem_spec n (y := 2#u64) (by decide))
    simp at hmv hrv
    have hlt : m.val < k := by omega
    simp [hm, hr, ih m.val hlt m rfl, h.add_ok]
    split_ifs with hodd
    · rw [← add_nsmul, ← succ_nsmul]; congr 2
      have := congrArg UScalar.val hodd; simp at this; omega
    · rw [← add_nsmul]; congr 2
      have : r.val ≠ 1 := fun e => hodd (UScalar.eq_of_val_eq (by simpa using e))
      omega

end double_and_add
