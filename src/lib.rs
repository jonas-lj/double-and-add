//! Scalar multiplication by repeated doubling and adding.

use num_traits::Zero;

/// Computes `scalar * base`, i.e. `base` added to itself `scalar` times, using the
/// left-to-right double-and-add algorithm.
///
/// A scalar of zero gives `T::zero()`.
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
