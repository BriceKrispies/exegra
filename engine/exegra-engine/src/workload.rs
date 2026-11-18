//! Open arrival processes of format 2 (WG-4715): the schedule of arrival instants of an open
//! workload, constant or Poisson, over phases with constant rates or ramps, repeated with a
//! period, stopping at the horizon. A port of `formal/Exegra/Workload.lean`; the Poisson
//! interarrival is computed on big integers, as the Lean definition is on `Nat`.

use num_bigint::{BigInt, BigUint, Sign};

/// A rate in instants per second: constant `num/den`, or a ramp from `n0/d0` to `n1/d1`.
#[derive(Clone, Debug)]
pub enum Rate {
    Const(u64, u64),
    Ramp(u64, u64, u64, u64),
}

impl Rate {
    pub fn ends(&self) -> ((u64, u64), (u64, u64)) {
        match *self {
            Rate::Const(a, b) => ((a, b), (a, b)),
            Rate::Ramp(a0, b0, a1, b1) => ((a0, b0), (a1, b1)),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Phase {
    pub start: u64,
    pub stop: u64,
    pub rate: Rate,
}

#[derive(Clone, Debug, Default)]
pub struct Cursor {
    pub rep: u64,
    pub phase: u64,
    pub j: u64,
    pub last: Option<u64>,
    pub done: bool,
}

/// Subtraction truncated at 0, as on Lean's `Nat`.
fn sat_sub(a: BigUint, b: &BigUint) -> BigUint {
    if &a < b {
        BigUint::from(0u32)
    } else {
        a - b
    }
}

fn big(x: u64) -> BigUint {
    BigUint::from(x)
}

/// `⌈√x⌉`.
fn ceil_sqrt(x: &BigUint) -> BigUint {
    if x == &BigUint::from(0u32) {
        BigUint::from(0u32)
    } else {
        (x - 1u32).sqrt() + 1u32
    }
}

/// `interarrival` for a sample `e` that fits 128 bits: machine integers for a constant rate
/// when nothing overflows, the big integers otherwise.
#[allow(clippy::too_many_arguments)]
pub fn interarrival_wide(
    p: u64,
    l: u64,
    a0: u64,
    b0: u64,
    a1: u64,
    b1: u64,
    d: u64,
    e: u128,
) -> Option<u64> {
    // A constant rate (no growth, `gn = 0`) in machine integers when nothing overflows.
    if u128::from(a1) * u128::from(b0) == u128::from(a0) * u128::from(b1) {
        let fast = (|| {
            let rd = u128::from(b0)
                .checked_mul(u128::from(b1))?
                .checked_mul(u128::from(l))?
                .checked_mul(u128::from(p))?;
            let rn = u128::from(a0)
                .checked_mul(u128::from(b1))?
                .checked_mul(u128::from(l))?;
            let rn64 = rn.checked_mul(1u128 << 64)?;
            let num = e.checked_mul(2)?.checked_mul(rd)?.checked_add(rn64)?;
            let den = rn64.checked_mul(2)?;
            if den == 0 {
                return Some(0);
            }
            Some(u64::try_from(num / den).unwrap_or(u64::MAX))
        })();
        if fast.is_some() {
            return fast;
        }
    }
    interarrival(p, l, a0, b0, a1, b1, d, &BigUint::from(e))
}

/// The Poisson interarrival from `d` base units into a phase of length `l` (Workload.lean,
/// `interarrival`); `None` when the mass left in a falling ramp is below the sample.
#[allow(clippy::too_many_arguments)]
pub fn interarrival(
    p: u64,
    l: u64,
    a0: u64,
    b0: u64,
    a1: u64,
    b1: u64,
    d: u64,
    e: &BigUint,
) -> Option<u64> {
    let two64 = BigUint::from(1u32) << 64;
    let rd = big(b0) * big(b1) * big(l) * big(p);
    let gn = BigInt::from(a1) * BigInt::from(b0) - BigInt::from(a0) * BigInt::from(b1);
    let rn_i = BigInt::from(a0) * BigInt::from(b1) * BigInt::from(l) + &gn * BigInt::from(d);
    let rn = rn_i.to_biguint().unwrap_or_default();
    let to_u64 = |x: BigUint| -> u64 { u64::try_from(x).unwrap_or(u64::MAX) };
    if gn.sign() == Sign::NoSign {
        let num = big(2) * e * &rd + &two64 * &rn;
        let den = big(2) * &two64 * &rn;
        if den == BigUint::from(0u32) {
            return Some(0);
        }
        return Some(to_u64(num / den));
    }
    let gabs = gn.magnitude().clone();
    let a = &rn * &two64;
    let c = &gabs * &two64;
    let sq = &rn * &rn * &two64 * &two64;
    let m = big(2) * &gabs * e * &rd * &two64;
    if gn.sign() == Sign::Plus {
        let inner: BigUint = big(4) * (&sq + &m);
        let root = inner.sqrt();
        let num = sat_sub(&c + root, &(big(2) * &a));
        Some(to_u64(num / (big(2) * &c)))
    } else if sq < m {
        None
    } else {
        let root = ceil_sqrt(&(big(4) * (&sq - &m)));
        let num = sat_sub(big(2) * &a + &c, &root);
        Some(to_u64(num / (big(2) * &c)))
    }
}

/// The fuel of `next_time`.
pub fn fuel_for(horizon: u64, phases: &[Phase]) -> u128 {
    (u128::from(horizon) + 2) * (phases.len() as u128 + 2)
}

/// The next arrival instant from the cursor (Workload.lean, `nextTime`): its time, the next
/// cursor, and how many samples of `ex` it used.
#[allow(clippy::too_many_arguments)]
pub fn next_time(
    p: u64,
    horizon: u64,
    phases: &[Phase],
    period: Option<u64>,
    poisson: bool,
    ex: &dyn Fn(u64) -> u128,
    mut fuel: u128,
    mut c: Cursor,
) -> (Option<u64>, Cursor, u64) {
    let mut used = 0u64;
    loop {
        if fuel == 0 {
            c.done = true;
            return (None, c, used);
        }
        fuel -= 1;
        if c.done {
            return (None, c, used);
        }
        let advance = |c: &mut Cursor| {
            c.phase += 1;
            c.j = 0;
            c.last = None;
        };
        let Some(ph) = usize::try_from(c.phase).ok().and_then(|k| phases.get(k)) else {
            match period {
                Some(_) => {
                    c.rep += 1;
                    c.phase = 0;
                    c.j = 0;
                    c.last = None;
                    continue;
                }
                None => {
                    c.done = true;
                    return (None, c, used);
                }
            }
        };
        let off = u128::from(c.rep) * u128::from(period.unwrap_or(0));
        let start = u128::from(ph.start) + off;
        let stop = u128::from(ph.stop) + off;
        if start >= u128::from(horizon) {
            c.done = true;
            return (None, c, used);
        }
        let ((a0, b0), (a1, b1)) = ph.rate.ends();
        if !poisson {
            if a0 == 0 {
                advance(&mut c);
                continue;
            }
            let t = start
                + (BigUint::from(c.j) * big(p) * big(b0) / big(a0))
                    .try_into()
                    .unwrap_or(u128::MAX / 2);
            if t >= stop || t >= u128::from(horizon) {
                advance(&mut c);
                continue;
            }
            c.j += 1;
            return (Some(t as u64), c, used);
        }
        if a0 == 0 && a1 == 0 {
            advance(&mut c);
            continue;
        }
        let base = c.last.map_or(start, u128::from);
        let e = ex(used);
        used += 1;
        match interarrival_wide(
            p,
            ph.stop.saturating_sub(ph.start),
            a0,
            b0,
            a1,
            b1,
            (base - start) as u64,
            e,
        ) {
            None => {
                advance(&mut c);
            }
            Some(s) => {
                let t = base + u128::from(s);
                if t >= stop || t >= u128::from(horizon) {
                    advance(&mut c);
                } else {
                    c.last = Some(t as u64);
                    return (Some(t as u64), c, used);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reference_values() {
        let ph = [Phase {
            start: 0,
            stop: 5000,
            rate: Rate::Const(1000, 1),
        }];
        let c = Cursor {
            j: 3,
            ..Cursor::default()
        };
        assert_eq!(
            next_time(1_000_000, 10000, &ph, None, false, &|_| 0u128, 100, c).0,
            Some(3000)
        );
        let one = BigUint::from(1u32) << 64;
        assert_eq!(
            interarrival(1_000_000, 1000, 1000, 1, 1000, 1, 0, &one),
            Some(1000)
        );
    }
}
