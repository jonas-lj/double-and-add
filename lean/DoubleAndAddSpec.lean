import DoubleAndAdd

/-!
Specs of the functions in `src/lib.rs`, proved directly on the Aeneas translation in
`DoubleAndAdd.lean`. Each spec is followed by `#check_axioms`, so this file fails to build if a
proof breaks or depends on a `sorry` or an `axiom`, such as a Rust function Aeneas cannot
translate.
-/

open Aeneas Aeneas.Std Result
open Lean Elab Command

/-- The axioms the proofs may depend on: Lean's standard axioms. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The axioms that `root` depends on, and the theorems it depends on whose proofs failed. Lean
records a proof that fails with an automatically inserted (synthetic) `sorry`. The search stops at
such a theorem, so `sorryAx` among the axioms means a hand-written `sorry`. -/
def collectDependencies (env : Environment) (root : Name) : Array Name × Array Name := Id.run do
  let mut visited : NameSet := {}
  let mut axs := #[]
  let mut failed := #[]
  let mut todo := #[root]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if visited.contains n then continue
    visited := visited.insert n
    let some info := env.find? n | continue
    if info matches .axiomInfo _ then
      axs := axs.push n
    else if (info.value? (allowOpaque := true)).any (·.hasSyntheticSorry) then
      failed := failed.push n
    else
      todo := todo ++ info.type.getUsedConstants
      if let some value := info.value? (allowOpaque := true) then
        todo := todo ++ value.getUsedConstants
  return (axs, failed)

/-- `#check_axioms foo` fails if `foo` depends on an axiom that is not in `allowedAxioms`, or on a
theorem whose proof failed. If the proof of `foo` itself failed, Lean has already reported it. -/
elab "#check_axioms " thm:ident : command => do
  let constName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo thm
  let (axs, failed) := collectDependencies (← getEnv) constName
  if failed.any (constName.isPrefixOf ·) then return
  unless failed.isEmpty do
    let failed := failed.map privateToUserName
    logError m!"'{constName}' depends on theorems whose proofs failed: {failed}"
  let disallowed := axs.filter (· ∉ allowedAxioms)
  unless disallowed.isEmpty do
    logError m!"'{constName}' depends on disallowed axioms: {disallowed}"

namespace double_and_add

variable {T : Type} [AddMonoid T]

/-- The Rust `Zero` instance implements the additive monoid structure on `T`: `zero` returns `0`
and `add` returns the sum, and neither fails. -/
structure ImplementsAddMonoid (zeroInst : num_traits.identities.Zero T) : Prop where
  zero_ok : zeroInst.zero = ok 0
  add_ok : ∀ a b, zeroInst.coreopsarithAddInst.add a b = ok (a + b)

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

#check_axioms double_and_add_spec

omit [AddMonoid T] in
private theorem eq_ok_of_spec {m : Result T} {v : T} (h : m ⦃ (· = v) ⦄) : m = ok v := by
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists h
  exact hr

/-- Correctness of multi-scalar multiplication: for any type whose `Zero` instance implements an
additive monoid, `multi_scalar_mul points scalars` succeeds and returns
`∑ i, scalars[i] • points[i]`, over the indices of the shorter slice. -/
theorem multi_scalar_mul_spec (zeroInst : num_traits.identities.Zero T)
    (copyInst : core.marker.Copy T) (h : ImplementsAddMonoid zeroInst)
    (points : Slice T) (scalars : Slice U64) :
    multi_scalar_mul zeroInst copyInst points scalars =
      ok ((points.val.zip scalars.val).map (fun (point, scalar) => scalar.val • point)).sum := by
  set terms := (points.val.zip scalars.val).map (fun (point, scalar) => scalar.val • point)
  unfold multi_scalar_mul multi_scalar_mul_loop
  simp only [h.zero_ok, core.slice.Slice.iter, core.iter.traits.iterator.Iterator.zip.trait_default,
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
        simp [hp, hs, double_and_add_spec zeroInst copyInst h, h.add_ok, WP.spec_ok]
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

#check_axioms multi_scalar_mul_spec

end double_and_add
