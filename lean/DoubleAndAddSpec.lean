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

/-! ## Specs for any additive monoid

`double_and_add` and `multi_scalar_mul` add their terms in a fixed order, so their specs hold for
any additive monoid `(T, +, 0)`, including ones where `+` is not commutative. -/

section Monoid

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

end Monoid

/-! ## Specs that need `+` to be commutative

`windowed_msm` doubles the accumulated sum `a₀ · P₀ + ⋯ + aₖ₋₁ · Pₖ₋₁` and adds new terms to it,
which only gives `2a₀ · P₀ + ⋯ + 2aₖ₋₁ · Pₖ₋₁` if `+` is commutative. Its specs therefore assume
an additive commutative monoid `(T, +, 0)`. -/

section CommMonoid

variable {T : Type} [AddCommMonoid T]
variable {zeroInst : num_traits.identities.Zero T} {copyInst : core.marker.Copy T}

/-- The doubling loop `for _ in 0..W { acc = acc + acc; }` returns `2^W · acc`. -/
private lemma doubling_loop [ImplementsAddMonoid zeroInst] (W : U32) (acc : T) :
    windowed_msm_loop0_loop0 zeroInst { start := 0#u32, «end» := W } acc =
      ok (2 ^ W.val • acc) := by
  unfold windowed_msm_loop0_loop0
  apply eq_ok_of_spec
  apply loop.spec_decr_nat
    (measure := fun x => W.val - x.1.start.val)
    (inv := fun x => x.1.«end» = W ∧ x.1.start.val ≤ W.val ∧ x.2 = 2 ^ x.1.start.val • acc)
  · rintro ⟨⟨i, e⟩, a⟩ ⟨he, hi, ha⟩
    dsimp only at he hi ha ⊢
    subst he ha
    unfold windowed_msm_loop0_loop0.body
    by_cases hlt : i.val < e.val
    · obtain ⟨⟨o, r⟩, hnext, ho, hr, hre⟩ := WP.spec_imp_exists
        (core.iter.range.IteratorRange.next_U32_some_spec { start := i, «end» := e } hlt)
      simp only at hr hre
      simp [hnext, ho, ImplementsAddMonoid.add_ok, WP.spec_ok]
      refine ⟨hre, by omega, ?_, by omega⟩
      rw [hr, pow_succ, mul_two, add_nsmul]
    · obtain ⟨⟨o, r⟩, hnext, ho, hr⟩ := WP.spec_imp_exists
        (core.iter.range.IteratorRange.next_U32_none_spec { start := i, «end» := e } (by simp; omega))
      simp [hnext, ho, WP.spec_ok]
      rw [show i.val = e.val by omega]
  · simp

/-- The loop `for (table, &scalar) in tables.iter().zip(scalars) { … }` adds
`dⱼ · Pⱼ` to `acc` for each `j`, where `dⱼ = ⌊sⱼ / 2^(window · W)⌋ mod 2^W` is the window's digit
of `sⱼ`. -/
private lemma digit_loop [ImplementsAddMonoid zeroInst] (W window : U32) {N : Usize}
    (points : List T) (tables : Slice (Array T N)) (scalars : Slice U64) (acc : T)
    (hshift : window.val * W.val < 64) (hN : N.val = 2 ^ W.val)
    (htables : tables.val.map (·.val) = points.map (fun point => (List.range N.val).map (· • point)))
    (hlen : points.length = scalars.length) :
    windowed_msm_loop0_loop1 W zeroInst ⟨⟨tables, 0⟩, ⟨scalars, 0⟩⟩ acc window =
      ok (acc + weightedSum (fun s : U64 => (s.val >>> (window.val * W.val)) % 2 ^ W.val)
        (points.zip scalars.val)) := by
  set f := fun s : U64 => (s.val >>> (window.val * W.val)) % 2 ^ W.val
  have htlen : tables.val.length = points.length := by simpa using congrArg List.length htables
  have hrow : ∀ j (hj : j < tables.val.length) d (hd : d < N.val),
      (tables.val[j]).val[d]'(by have := (tables.val[j]).property; simp_all) = d • points[j] := by
    intro j hj d hd
    have := List.getElem_of_eq htables (i := j) (by simpa using hj)
    simp at this
    simp [this]
  unfold windowed_msm_loop0_loop1
  apply eq_ok_of_spec
  apply loop.spec_decr_nat
    (measure := fun x => tables.val.length - x.1.fst.i)
    (inv := fun x => x.1.fst.slice = tables ∧ x.1.snd = ⟨scalars, x.1.fst.i⟩ ∧
      x.2 + weightedSum f ((points.zip scalars.val).drop x.1.fst.i) =
        acc + weightedSum f (points.zip scalars.val))
  · rintro ⟨⟨⟨ts, i⟩, ss⟩, a⟩ ⟨hts, hss, ha⟩
    dsimp only at hts hss ha ⊢
    subst hts hss
    unfold windowed_msm_loop0_loop1.body
    simp only [core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
      core.slice.iter.IteratorSliceIter.next]
    by_cases hp : i < ts.val.length
    · by_cases hs : i < scalars.val.length
      · simp only [hp, hs, Slice.len_val, ↓reduceDIte, bind_tc_ok, bind_ok]
        have hN1 : 1 ≤ N.val := by rw [hN]; exact Nat.one_le_two_pow
        step as ⟨sh, hsh⟩
        step as ⟨i1, hi1, _⟩
        step with UScalar.cast_inBounds_spec .U64 N (Usize.val_le_U64_max N) as ⟨i2, hi2⟩
        step as ⟨i3, hi3⟩
        step as ⟨d, hd, _⟩
        have hdlt : d.val < N.val := by
          rw [hd, UScalar.val_and, hi3, hi2, hN]
          simp [Nat.and_two_pow_sub_one_eq_mod]
          exact Nat.mod_lt _ (Nat.two_pow_pos _)
        step with UScalar.cast_inBounds_spec .Usize d (by scalar_tac) as ⟨i4, hi4⟩
        step as ⟨t, ht⟩
        have hdv : d.val = f scalars.val[i] := by
          rw [hd, UScalar.val_and, hi3, hi2, hi1, hsh, hN]
          simp [f, Nat.and_two_pow_sub_one_eq_mod]
          rfl
        have hzlen : i < (points.zip scalars.val).length := by simp; omega
        rw [List.drop_eq_getElem_cons hzlen] at ha
        simp only [List.getElem_zip] at ha
        rw [weightedSum_cons] at ha
        simp [ImplementsAddMonoid.add_ok, WP.spec_ok]
        have ht' : t = f scalars.val[i] • points[i] := by
          rw [← hdv, ← hrow i hp d.val hdlt, ht]
          simp only [hi4]
          rfl
        refine ⟨?_, by omega⟩
        rw [ht', add_assoc]
        exact ha
      · have : points.length = scalars.val.length := hlen
        exact absurd (by omega) hs
    · have hnil : (points.zip scalars.val).drop i = [] := List.drop_eq_nil_of_le (by simp; omega)
      rw [hnil, weightedSum_nil, add_zero] at ha
      simp [hp, WP.spec_ok, ha]
  · simp

/-- The loop `for window in (0..w).rev() { … }`, started with the accumulator
`Σ ⌊sⱼ / 2^(w · W)⌋ · Pⱼ`, returns `Σ sⱼ · Pⱼ`. -/
private lemma window_loop [ImplementsAddMonoid zeroInst] (W windows : U32) {N : Usize}
    (points : List T) (tables : Slice (Array T N)) (scalars : Slice U64)
    (hshift : (windows.val - 1) * W.val < 64) (hN : N.val = 2 ^ W.val)
    (htables : tables.val.map (·.val) = points.map (fun point => (List.range N.val).map (· • point)))
    (hlen : points.length = scalars.length) :
    windowed_msm_loop0 W zeroInst ⟨{ start := 0#u32, «end» := windows }⟩ tables scalars
      (weightedSum (fun s : U64 => s.val >>> (windows.val * W.val)) (points.zip scalars.val)) =
    ok (weightedSum (fun s : U64 => s.val) (points.zip scalars.val)) := by
  unfold windowed_msm_loop0
  apply eq_ok_of_spec
  apply loop.spec_decr_nat
    (measure := fun x => x.1.iter.«end».val)
    (inv := fun x => x.1.iter.start = 0#u32 ∧ x.1.iter.«end».val ≤ windows.val ∧
      x.2 = weightedSum (fun s : U64 => s.val >>> (x.1.iter.«end».val * W.val))
        (points.zip scalars.val))
  · rintro ⟨⟨⟨st, w⟩⟩, a⟩ ⟨hst, hw, ha⟩
    dsimp only at hst hw ha ⊢
    subst hst
    unfold windowed_msm_loop0.body
    by_cases hpos : 0 < w.val
    · obtain ⟨w1, hw1v, hnext⟩ := rev_range_next_some { start := 0#u32, «end» := w } (by simpa)
      simp only at hw1v
      have hw1 : w1.val * W.val < 64 :=
        lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) hshift
      rw [hnext]
      simp only [bind_tc_ok, bind_ok, doubling_loop, core.slice.Slice.iter,
        core.iter.traits.iterator.Iterator.zip.trait_default,
        core.iter.traits.iterator.Iterator.zip.default,
        SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter]
      simp [digit_loop W w1 points tables scalars _ hw1 hN htables hlen, WP.spec_ok]
      refine ⟨by omega, ?_, by omega⟩
      have hw' : w.val = w1.val + 1 := by omega
      rw [ha, hw', ← weightedSum_mul, ← weightedSum_add]
      exact weightedSum_congr _ fun s => shiftRight_succ_mul s.val w1.val W.val
    · rw [rev_range_next_none { start := 0#u32, «end» := w } (by simpa using hpos)]
      have hw0 : w.val = 0 := by omega
      simp [WP.spec_ok, ha, hw0]
  · simp

/-- The check `N as u64 == 1 << W` in `windowed_msm` succeeds in computing both sides, and they are
equal exactly when `N = 2^W`. -/
private lemma table_size_check (W : U32) (N : Usize) (h2 : W.val < 64) :
    ∃ c sh, lift (UScalar.cast .U64 N) = ok c ∧ 1#u64 <<< W = ok sh ∧
      (c = sh ↔ N.val = 2 ^ W.val) := by
  obtain ⟨c, hc, hcv⟩ := WP.spec_imp_exists
    (UScalar.cast_inBounds_spec .U64 N (Usize.val_le_U64_max N))
  obtain ⟨sh, hsh, hshv, -⟩ := WP.spec_imp_exists (U64.ShiftLeft_spec 1#u64 W (by simpa using h2))
  have hshv' : sh.val = 2 ^ W.val := by
    rw [hshv]
    simp [Nat.shiftLeft_eq, U64.size]
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by simpa [U64.numBits] using h2))
  refine ⟨c, sh, hc, hsh, ⟨fun e => ?_, fun e => UScalar.eq_of_val_eq ?_⟩⟩
  · rw [← hcv, e, hshv']
  · rw [hcv, hshv', e]

/-- **Correctness of `windowed_msm`.**

Let `(T, +, 0)` be an additive *commutative* monoid whose Rust `Zero` and `Add` implementations
compute `0` and `+` (`ImplementsAddMonoid`). Let `1 ≤ W ≤ 63` and `N = 2^W`. Let `P₀, …, Pₖ₋₁ ∈ T`,
let `tⱼ` be the table `(0 · Pⱼ, 1 · Pⱼ, …, (N − 1) · Pⱼ)`, and let `s = (s₀, …, sₖ₋₁)` be `u64`
values. Then `windowed_msm::<W, N>((t₀, …, tₖ₋₁), s)` returns

  `s₀ · P₀ + s₁ · P₁ + ⋯ + sₖ₋₁ · Pₖ₋₁`  (`0` if `k = 0`). -/
theorem windowed_msm_spec [ImplementsAddMonoid zeroInst] (W : U32) {N : Usize} (points : List T)
    (tables : Slice (Array T N)) (scalars : Slice U64) :
    0 < W.val → W.val < 64 → N.val = 2 ^ W.val →
    tables.val.map (·.val) = points.map (fun point => (List.range N.val).map (· • point)) →
    points.length = scalars.length →
    windowed_msm W zeroInst copyInst tables scalars =
      ok ((points.zip scalars.val).map (fun (point, scalar) => scalar.val • point)).sum := by
  intro h1 h2 hN htables hlen
  obtain ⟨c, sh, hc, hsh, hiff⟩ := table_size_check W N h2
  have htlen : tables.length = scalars.length := by
    rw [← hlen]; simpa using congrArg List.length htables
  have hlen' : Slice.len tables = Slice.len scalars :=
    UScalar.eq_of_val_eq (by simpa using htlen)
  unfold windowed_msm
  simp only [massert, show (0#u32 < W) = True by simp; omega,
    show (W < core.num.U64.BITS) = True by simp; omega, ↓reduceIte, hc, hsh, hiff.mpr hN, hlen',
    ImplementsAddMonoid.zero_ok, bind_ok]
  apply eq_ok_of_spec
  -- The loop over the windows computes the result when started with `0` at any window `nw` with
  -- `(nw - 1) · W < 64 ≤ nw · W`.
  have hloop : ∀ nw : U32, 64 ≤ nw.val * W.val → (nw.val - 1) * W.val < 64 →
      windowed_msm_loop0 W zeroInst ⟨{ start := 0#u32, «end» := nw }⟩ tables scalars 0 ⦃ x =>
        x = ((points.zip scalars.val).map (fun (point, scalar) => scalar.val • point)).sum ⦄ := by
    intro nw hge hlt
    have h0 : (0 : T) =
        weightedSum (fun s : U64 => s.val >>> (nw.val * W.val)) (points.zip scalars.val) := by
      rw [weightedSum_congr (g := fun _ => 0) _ fun s => ?_, weightedSum_zero]
      have : s.val < 2 ^ 64 := by scalar_tac
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt (lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) hge))
    rw [h0, window_loop W nw points tables scalars hlt hN htables hlen, WP.spec_ok]
    rfl
  -- The number of windows is `⌈64 / W⌉ = ⌊(64 + W − 1) / W⌋`.
  step as ⟨x, hx⟩
  step as ⟨y, hy⟩
  step as ⟨q, hq⟩
  simp only [UScalarTy.numBits] at hx
  have hdm := Nat.div_add_mod y.val W.val
  have hml := Nat.mod_lt y.val h1
  have hqW : q.val * W.val = W.val * (y.val / W.val) := by rw [hq, Nat.mul_comm]
  simp only [core.iter.traits.iterator.Iterator.rev.trait_default,
    core.iter.traits.iterator.Iterator.rev.default, bind_ok]
  apply hloop q
  · omega
  · rw [Nat.sub_mul, one_mul]; omega

omit [AddCommMonoid T] in
/-- **`windowed_msm` rejects invalid window parameters.**

For any type `T`, with no assumption on its Rust trait implementations: unless `1 ≤ W ≤ 63` and
`N = 2^W`, `windowed_msm::<W, N>(t, s)` panics with a failed assertion. -/
theorem windowed_msm_invalid_window (W : U32) {N : Usize} (tables : Slice (Array T N))
    (scalars : Slice U64) :
    ¬(0 < W.val ∧ W.val < 64 ∧ N.val = 2 ^ W.val) →
    windowed_msm W zeroInst copyInst tables scalars = fail .assertionFailure := by
  intro hbad
  unfold windowed_msm
  by_cases h1 : 0 < W.val
  · by_cases h2 : W.val < 64
    · obtain ⟨c, sh, hc, hsh, hiff⟩ := table_size_check W N h2
      have hne : c ≠ sh := fun e => hbad ⟨h1, h2, hiff.mp e⟩
      simp [massert, h1, h2, hc, hsh, hne]
    · simp [massert, h1, h2]
  · simp [massert, h1]

omit [AddCommMonoid T] in
/-- **`windowed_msm` rejects slices of different lengths.**

For any type `T`, with no assumption on its Rust trait implementations, and all slices `t` of
tables and `s` of `u64` values with `|t| ≠ |s|`, `windowed_msm::<W, N>(t, s)` panics with a failed
assertion. -/
theorem windowed_msm_length_mismatch (W : U32) {N : Usize} (tables : Slice (Array T N))
    (scalars : Slice U64) :
    tables.length ≠ scalars.length →
    windowed_msm W zeroInst copyInst tables scalars = fail .assertionFailure := by
  intro hlen
  by_cases hvalid : 0 < W.val ∧ W.val < 64 ∧ N.val = 2 ^ W.val
  · obtain ⟨h1, h2, hN⟩ := hvalid
    obtain ⟨c, sh, hc, hsh, hiff⟩ := table_size_check W N h2
    have hlen' : Slice.len tables ≠ Slice.len scalars := fun e => hlen (by
      simpa using congrArg UScalar.val e)
    unfold windowed_msm
    simp [massert, h1, h2, hc, hsh, hiff.mpr hN, hlen']
  · exact windowed_msm_invalid_window W tables scalars hvalid

end CommMonoid

end double_and_add
