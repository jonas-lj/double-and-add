import Common
import DoubleAndAdd

/-!
Specs of the functions in `src/lib.rs`, proved directly on the Aeneas translation in
`DoubleAndAdd.lean`. `CheckAxioms.lean` checks that every theorem here depends only on the allowed
axioms.
-/

open Aeneas Aeneas.Std Result

namespace double_and_add

variable {T : Type} [AddMonoid T]

/-- The Rust `Zero` instance implements the additive monoid structure on `T`: `zero` returns `0`
and `add` returns the sum, and neither fails. -/
class ImplementsAddMonoid (zeroInst : num_traits.identities.Zero T) : Prop where
  zero_ok : zeroInst.zero = ok 0
  add_ok : ∀ a b, zeroInst.coreopsarithAddInst.add a b = ok (a + b)

variable {zeroInst : num_traits.identities.Zero T} {copyInst : core.marker.Copy T}

/-- Correctness of double-and-add: for any type whose `Zero` instance implements an additive
monoid, `double_and_add base n` succeeds and returns `n • base`. -/
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

/-- Correctness of multi-scalar multiplication: for any type whose `Zero` instance implements an
additive monoid, `multi_scalar_mul points scalars` succeeds and returns
`∑ i, scalars[i] • points[i]`, over the indices of the shorter slice. -/
theorem multi_scalar_mul_spec [ImplementsAddMonoid zeroInst] (points : Slice T)
    (scalars : Slice U64) :
    multi_scalar_mul zeroInst copyInst points scalars =
      ok ((points.val.zip scalars.val).map (fun (point, scalar) => scalar.val • point)).sum := by
  set terms := (points.val.zip scalars.val).map (fun (point, scalar) => scalar.val • point)
  unfold multi_scalar_mul multi_scalar_mul_loop
  simp only [ImplementsAddMonoid.zero_ok, core.slice.Slice.iter, core.iter.traits.iterator.Iterator.zip.trait_default,
    core.iter.traits.iterator.Iterator.zip.default,
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter, bind_ok, bind_tc_ok]
  apply eq_ok_of_spec
  -- Loop invariant: both iterators are at the same index `i`, and the accumulator plus the terms
  -- from index `i` on is the full sum.
  apply loop.spec_decr_nat
    (measure := fun x => points.val.length - x.1.fst.i)
    (inv := fun x => x.1.fst.slice = points ∧ x.1.snd = ⟨scalars, x.1.fst.i⟩ ∧
      x.2 + (terms.drop x.1.fst.i).sum = terms.sum)
  · rintro ⟨⟨⟨ps, i⟩, ss⟩, acc⟩ ⟨hps, hss, hacc⟩
    dsimp only at hps hss hacc ⊢
    subst hps hss
    unfold multi_scalar_mul_loop.body
    simp only [core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
      core.slice.iter.IteratorSliceIter.next]
    by_cases hp : i < ps.val.length
    · by_cases hs : i < scalars.val.length
      · have hlen : i < terms.length := by simp [terms]; omega
        rw [List.drop_eq_getElem_cons hlen] at hacc
        simp [hp, hs, double_and_add_spec, ImplementsAddMonoid.add_ok, WP.spec_ok]
        refine ⟨?_, by omega⟩
        simp only [terms, List.sum_cons, List.getElem_map, List.getElem_zip] at hacc
        rw [add_assoc]
        exact hacc
      · have hnil : terms.drop i = [] := List.drop_eq_nil_of_le (by simp [terms]; omega)
        simp [hp, hs, WP.spec_ok]
        simpa [hnil] using hacc
    · have hnil : terms.drop i = [] := List.drop_eq_nil_of_le (by simp [terms]; omega)
      simp [hp, WP.spec_ok]
      simpa [hnil] using hacc
  · simp

end double_and_add
