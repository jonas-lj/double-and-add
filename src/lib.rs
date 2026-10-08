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

/// Computes the multi-scalar multiplication `scalars[0] * P_0 + scalars[1] * P_1 + ...` with a
/// window of `W` bits, where `tables[j][i]` must be `i * P_j` for `i` in `0..N` and `N = 2^W`.
/// `+` on `T` must be commutative.
///
/// # Panics
///
/// Panics if `W` is not between 1 and 63, if `N` is not `2^W`, or if `tables` and `scalars` have
/// different lengths.
pub fn windowed_msm<T, const W: u32, const N: usize>(tables: &[[T; N]], scalars: &[u64]) -> T
where
    T: Zero + Copy,
{
    assert!(0 < W && W < u64::BITS);
    assert!(N as u64 == 1 << W);
    assert!(tables.len() == scalars.len());
    let mut acc = T::zero();
    // The number of windows, `ceil(64 / W)`. Not `u64::BITS.div_ceil(W)`, since Aeneas has no
    // model of `u32::div_ceil`.
    #[allow(clippy::manual_div_ceil)]
    let mut window = (u64::BITS + W - 1) / W;
    while window > 0 {
        window -= 1;
        for _ in 0..W {
            acc = acc + acc;
        }
        for (table, &scalar) in tables.iter().zip(scalars) {
            let digit = (scalar >> (window * W)) & (N as u64 - 1);
            acc = acc + table[digit as usize];
        }
    }
    acc
}
