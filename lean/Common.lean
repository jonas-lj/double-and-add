import Aeneas

/-!
Project-wide definitions used by the specs, kept out of the spec files so those contain only
what needs reviewing.
-/

open Aeneas Aeneas.Std Result

/-- Converts a spec in Aeneas's `⦃ ⦄` form, as produced by `loop.spec_decr_nat`, to `= ok`. -/
lemma eq_ok_of_spec {α : Type} {m : Result α} {v : α} (h : m ⦃ (· = v) ⦄) : m = ok v := by
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists h
  exact hr

/-- A `usize` value always fits in a `u64`, whether `usize` has 32 or 64 bits. -/
lemma Usize.val_le_U64_max (x : Usize) : x.val ≤ UScalar.max .U64 := by
  have : x.val ≤ Usize.max := by scalar_tac
  rcases Usize.bounds_eq with h | h <;> simp [h, U32.max_eq, U64.max_eq] at this ⊢ <;> omega

/-! ## Reversed ranges -/

/-- `(start..end).rev().next()` on `u32`, non-empty case: yields `end - 1` and shrinks the range. -/
lemma rev_range_next_some (r : core.ops.range.Range U32) (h : r.start.val < r.«end».val) :
    ∃ e : U32, e.val = r.«end».val - 1 ∧
      core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
        (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepU32) ⟨r⟩ =
      ok (some e, ⟨{ start := r.start, «end» := e }⟩) := by
  refine ⟨UScalar.ofNatCore (r.«end».val - 1) (by scalar_tac), by simp, ?_⟩
  have h1 : 1 ≤ r.«end».val := by omega
  simp [core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
    core.iter.range.UScalarStep, core.iter.range.UScalarStep.backward_checked,
    core.cmp.impls.PartialOrdU32.lt, h, h1]

/-- `(start..end).rev().next()` on `u32`, empty case: yields nothing. -/
lemma rev_range_next_none (r : core.ops.range.Range U32) (h : ¬ r.start.val < r.«end».val) :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepU32) ⟨r⟩ =
    ok (none, ⟨r⟩) := by
  simp [core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
    core.iter.range.UScalarStep, core.cmp.impls.PartialOrdU32.lt, h]

/-! ## Weighted sums -/

/-- `weightedSum f [(x₀, c₀), (x₁, c₁), …] = f c₀ • x₀ + f c₁ • x₁ + ⋯`. -/
def weightedSum {T C : Type} [AddMonoid T] (f : C → ℕ) (pairs : List (T × C)) : T :=
  (pairs.map fun (x, c) => f c • x).sum

lemma weightedSum_nil {T C : Type} [AddMonoid T] (f : C → ℕ) :
    weightedSum f ([] : List (T × C)) = 0 := rfl

lemma weightedSum_cons {T C : Type} [AddMonoid T] (f : C → ℕ) (x : T) (c : C)
    (pairs : List (T × C)) :
    weightedSum f ((x, c) :: pairs) = f c • x + weightedSum f pairs := rfl

lemma weightedSum_zero {T C : Type} [AddMonoid T] (pairs : List (T × C)) :
    weightedSum (fun _ => 0) pairs = 0 := by
  simp [weightedSum]

lemma weightedSum_add {T C : Type} [AddCommMonoid T] (f g : C → ℕ) (pairs : List (T × C)) :
    weightedSum (fun c => f c + g c) pairs = weightedSum f pairs + weightedSum g pairs := by
  induction pairs with
  | nil => simp [weightedSum]
  | cons p ps ih =>
    obtain ⟨x, c⟩ := p
    rw [weightedSum_cons, weightedSum_cons, weightedSum_cons, ih, add_nsmul]
    abel

lemma weightedSum_mul {T C : Type} [AddCommMonoid T] (k : ℕ) (f : C → ℕ)
    (pairs : List (T × C)) :
    weightedSum (fun c => k * f c) pairs = k • weightedSum f pairs := by
  induction pairs with
  | nil => simp [weightedSum]
  | cons p ps ih =>
    obtain ⟨x, c⟩ := p
    rw [weightedSum_cons, weightedSum_cons, ih, smul_add, smul_smul]

lemma weightedSum_congr {T C : Type} [AddMonoid T] {f g : C → ℕ} (pairs : List (T × C))
    (h : ∀ c, f c = g c) : weightedSum f pairs = weightedSum g pairs := by
  simp [weightedSum, h]

/-! ## Digits -/

/-- Splitting off the lowest `w` bits of `x >>> (i * w)`. -/
lemma shiftRight_succ_mul (x i w : ℕ) :
    2 ^ w * (x >>> ((i + 1) * w)) + (x >>> (i * w)) % 2 ^ w = x >>> (i * w) := by
  rw [Nat.add_mul, one_mul, Nat.shiftRight_add, Nat.shiftRight_eq_div_pow (x >>> (i * w)) w]
  exact Nat.div_add_mod _ _

/-! ## Axiom check

Checks that theorems depend only on the allowed axioms. A `sorry` shows up as the axiom `sorryAx`,
and an `axiom` declaration as itself, for example a Rust function that Aeneas could not translate.
-/

open Lean Elab Command

/-- The axioms that proofs may depend on: Lean's standard axioms. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- `#check_axioms_in M` fails if a theorem declared in module `M` depends on an axiom that is not
in `allowedAxioms`. Private and auxiliary theorems are checked through the theorems using them. -/
elab "#check_axioms_in " mod:ident : command => do
  let env ← getEnv
  let some modIdx := env.getModuleIdx? mod.getId
    | throwError "unknown module '{mod.getId}'"
  let theorems := env.constants.map₁.toList.filterMap fun (n, info) =>
    if info matches .thmInfo _ && !n.isInternal && env.getModuleIdxFor? n == some modIdx then
      some n
    else
      none
  if theorems.isEmpty then
    throwError "no theorems found in module '{mod.getId}'"
  for thm in theorems.toArray.qsort Name.lt do
    let axs ← liftCoreM <| collectAxioms thm
    let disallowed := axs.filter (· ∉ allowedAxioms)
    unless disallowed.isEmpty do
      let line := (← liftCoreM <| findDeclarationRanges? thm).map (·.range.pos.line)
      logError m!"'{thm}' ({mod.getId}.lean:{line.getD 0}) depends on disallowed axioms: \
        {disallowed}"
