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
    if scalar == 1 {
        base
    } else {
        let half = double_and_add(base, scalar / 2);
        if scalar % 2 == 1 {
            half + half + base
        } else {
            half + half
        }
    }
}

/// Computes the multi-scalar multiplication `scalars[0] * points[0] + scalars[1] * points[1] + ...`.
///
/// # Panics
///
/// Panics if `points` and `scalars` have different lengths.
pub fn multi_scalar_mul<T>(points: &[T], scalars: &[u64]) -> T
where
    T: Zero + Copy,
{
    assert!(points.len() == scalars.len());
    let mut acc = T::zero();
    for (&point, &scalar) in points.iter().zip(scalars) {
        acc = acc + double_and_add(point, scalar);
    }
    acc
}
