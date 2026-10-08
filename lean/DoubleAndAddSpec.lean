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

/-- **Base case of `double_and_add`.**

Under `ImplementsAddMonoid`, `double_and_add(b, 0)` returns `0` for all `b ∈ T`. -/
theorem double_and_add_zero [ImplementsAddMonoid zeroInst] (base : T) :
    double_and_add zeroInst copyInst base 0#u64 = ok 0 := by
  unfold double_and_add
  simp [ImplementsAddMonoid.zero_ok]

/-- **Recursive case of `double_and_add`.**

Under `ImplementsAddMonoid`, for all `b, h ∈ T` and `n ∈ {1, …, 2⁶⁴ − 1}`: if
`double_and_add(b, ⌊n / 2⌋)` returns `h`, then `double_and_add(b, n)` returns `h + h + b` if `n` is
odd, and `h + h` if `n` is even. -/
theorem double_and_add_step [ImplementsAddMonoid zeroInst] (base half : T) (n : U64) :
    n.val ≠ 0 →
    (∀ m : U64, m.val = n.val / 2 → double_and_add zeroInst copyInst base m = ok half) →
    double_and_add zeroInst copyInst base n =
      ok (if n.val % 2 = 1 then half + half + base else half + half) := by
  intro hn hrec
  have h0 : n ≠ 0#u64 := fun e => hn (by simp [e])
  obtain ⟨m, hm, hmv⟩ := WP.spec_imp_exists (U64.div_spec n (y := 2#u64) (by decide))
  obtain ⟨r, hr, hrv⟩ := WP.spec_imp_exists (U64.rem_spec n (y := 2#u64) (by decide))
  simp at hmv hrv
  have hodd : r = 1#u64 ↔ n.val % 2 = 1 := by
    constructor
    · intro e; have := congrArg UScalar.val e; simp at this; omega
    · intro e; exact UScalar.eq_of_val_eq (by simp; omega)
  unfold double_and_add
  simp only [h0, if_false, hm, hr, ImplementsAddMonoid.add_ok]
  by_cases ho : n.val % 2 = 1 <;> simp [ho, hodd, hrec m hmv]

/-- **Correctness of `double_and_add`.**

Let `(T, +, 0)` be an additive monoid whose Rust `Zero` and `Add` implementations compute `0` and
`+` (`ImplementsAddMonoid`). Then for all `b ∈ T` and all `n ∈ {0, …, 2⁶⁴ − 1}`,
`double_and_add(b, n)` returns

  `n · b = b + b + ⋯ + b`  (`n` terms; `0` if `n = 0`). -/
theorem double_and_add_spec [ImplementsAddMonoid zeroInst] (base : T) (n : U64) :
    double_and_add zeroInst copyInst base n = ok (n.val • base) := by
  induction hk : n.val using Nat.strong_induction_on generalizing n with
  | _ k ih =>
  by_cases hn : n.val = 0
  · obtain rfl : n = 0#u64 := UScalar.eq_of_val_eq (by simpa using hn)
    subst hk
    simp [double_and_add_zero]
  · rw [double_and_add_step base ((k / 2) • base) n hn
      (fun m hm => by rw [ih m.val (by omega) m rfl, hm, hk])]
    split_ifs
    · rw [← add_nsmul, ← succ_nsmul]; congr 2; omega
    · rw [← add_nsmul]; congr 2; omega

/-- **Correctness of `multi_scalar_mul`.**

Let `(T, +, 0)` be an additive monoid whose Rust `Zero` and `Add` implementations compute `0` and
`+` (`ImplementsAddMonoid`). Then for all `k` and all slices `p = (p₀, …, pₖ₋₁)` of elements of `T`
and `s = (s₀, …, sₖ₋₁)` of `u64` values, of the same length `k`, `multi_scalar_mul(p, s)` returns

  `s₀ · p₀ + s₁ · p₁ + ⋯ + sₖ₋₁ · pₖ₋₁`  (in this order; `0` if `k = 0`). -/
theorem multi_scalar_mul_spec [ImplementsAddMonoid zeroInst] (points : Slice T)
    (scalars : Slice U64) :
    points.length = scalars.length →
    multi_scalar_mul zeroInst copyInst points scalars =
      ok ((points.val.zip scalars.val).map (fun (point, scalar) => scalar.val • point)).sum := by
  intro hlen
  set terms := (points.val.zip scalars.val).map (fun (point, scalar) => scalar.val • point)
  have hlen' : Slice.len points = Slice.len scalars := UScalar.eq_of_val_eq (by simp [hlen])
  unfold multi_scalar_mul multi_scalar_mul_loop
  simp only [hlen', massert, ↓reduceIte, ImplementsAddMonoid.zero_ok, core.slice.Slice.iter, core.iter.traits.iterator.Iterator.zip.trait_default,
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

omit [AddMonoid T] in
/-- **`multi_scalar_mul` rejects slices of different lengths.**

For any type `T`, with no assumption on its Rust trait implementations, and all slices `p` of
elements of `T` and `s` of `u64` values with `|p| ≠ |s|`, `multi_scalar_mul(p, s)` panics with a
failed assertion. -/
theorem multi_scalar_mul_length_mismatch (points : Slice T) (scalars : Slice U64) :
    points.length ≠ scalars.length →
    multi_scalar_mul zeroInst copyInst points scalars = fail .assertionFailure := by
  intro hlen
  have hlen' : Slice.len points ≠ Slice.len scalars := fun e => hlen (by
    simpa using congrArg UScalar.val e)
  simp [multi_scalar_mul, massert, hlen']

end double_and_add
