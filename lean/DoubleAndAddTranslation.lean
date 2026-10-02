import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SplitIfs

/-!
A hand-written Lean translation of `double_and_add` from `src/lib.rs`, kept close to the Rust:

```rust
pub fn double_and_add<T>(base: T, scalar: u64) -> T
where
    T: Zero + Copy,
{
    if scalar == 0 {
        T::zero()
    } else {
        let half = double_and_add(base, scalar / 2);
        if scalar % 2 == 1 {
            half + half + base
        } else {
            half + half
        }
    }
}
```

Unlike the Aeneas translation in `DoubleAndAdd.lean`, nothing here can fail, so there is no
`Result`, and `T` is directly a Mathlib `AddMonoid` instead of a type with Rust trait instances.
The scalar is a natural number: the function only halves it, so it never overflows a `u64`.
-/

namespace DoubleAndAddTranslation

variable {T : Type} [AddMonoid T]

def doubleAndAdd (base : T) (scalar : ℕ) : T :=
  if scalar = 0 then
    0
  else
    let half := doubleAndAdd base (scalar / 2)
    if scalar % 2 = 1 then
      half + half + base
    else
      half + half

/-- Correctness of double-and-add: it computes `scalar • base`, i.e. `base` added to itself
`scalar` times. -/
theorem doubleAndAdd_spec (base : T) (scalar : ℕ) :
    doubleAndAdd base scalar = scalar • base := by
  induction scalar using Nat.strongRecOn with
  | _ n ih =>
    unfold doubleAndAdd
    dsimp only
    split_ifs with hzero hodd
    · rw [hzero, zero_nsmul]
    · rw [ih (n / 2) (by omega), ← add_nsmul, ← succ_nsmul]
      congr 1
      omega
    · rw [ih (n / 2) (by omega), ← add_nsmul]
      congr 1
      omega

end DoubleAndAddTranslation
