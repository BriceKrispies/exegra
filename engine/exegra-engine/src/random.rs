//! Seeded randomness of format 2 (`docs/simulation.md`, "Randomness"), as defined in
//! `formal/Exegra/Random.lean`: SplitMix64 as a family of named streams, FNV-1a 64,
//! `uniformInt`, integer tables and categorical choice.

/// The golden gamma of SplitMix64.
pub const GAMMA: u64 = 0x9E37_79B9_7F4A_7C15;

/// SplitMix64's output function.
pub fn mix64(z: u64) -> u64 {
    let z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    let z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// 64-bit FNV-1a over the UTF-8 bytes of a string.
pub fn fnv1a64(s: &str) -> u64 {
    s.bytes().fold(0xCBF2_9CE4_8422_2325, |h, b| {
        (h ^ u64::from(b)).wrapping_mul(0x0100_0000_01B3)
    })
}

/// The key of stream `name` under `seed`.
pub fn stream_key(seed: u64, name: &str) -> u64 {
    mix64(seed ^ fnv1a64(name))
}

/// The `i`-th draw (from 0) of a stream with key `k`.
pub fn draw_at(k: u64, i: u64) -> u64 {
    mix64(k.wrapping_add(i.wrapping_add(1).wrapping_mul(GAMMA)))
}

/// The `i`-th draw of stream `name` under `seed`.
pub fn draw(seed: u64, name: &str, i: u64) -> u64 {
    draw_at(stream_key(seed, name), i)
}

/// `uniformInt(lo, hi) = lo + ((r · (hi − lo + 1)) >> 64)`, for `lo ≤ hi < 2^64`.
pub fn uniform_int(r: u64, lo: u64, hi: u64) -> u64 {
    let span = u128::from(hi - lo) + 1;
    lo + ((u128::from(r) * span) >> 64) as u64
}

/// A drawn index into `n ≥ 1` values.
pub fn index(r: u64, n: usize) -> usize {
    uniform_int(r, 0, n.saturating_sub(1) as u64) as usize
}

/// Sample an integer table `[[u, x], ...]` (`u` strictly increasing from 0 to 2^32).
pub fn sample_table(r: u64, points: &[(u64, u64)]) -> u64 {
    let u = r >> 32;
    for w in points.windows(2) {
        let ((u0, x0), (u1, x1)) = (w[0], w[1]);
        if u < u1 {
            let d = u128::from(u - u0) * u128::from(x1 - x0) / u128::from(u1 - u0);
            return x0 + d as u64;
        }
    }
    points.last().map_or(0, |p| p.1)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn vigna_reference() {
        let out: Vec<u64> = (0..5).map(|i| draw_at(1_234_567, i)).collect();
        assert_eq!(
            out,
            [
                6_457_827_717_110_365_317,
                3_203_168_211_198_807_973,
                9_817_491_932_198_370_423,
                4_593_380_528_125_082_431,
                16_408_922_859_458_223_821
            ]
        );
    }

    #[test]
    fn fnv_and_streams() {
        assert_eq!(fnv1a64(""), 0xCBF2_9CE4_8422_2325);
        assert_eq!(fnv1a64("a"), 0xAF63_DC4C_8601_EC8C);
        assert_eq!(fnv1a64("foobar"), 0x8594_4171_F739_67E8);
        assert_eq!(stream_key(42, "demand:db:t:0"), 6_535_567_660_793_705_486);
        assert_eq!(draw(42, "demand:db:t:0", 0), 10_373_339_710_906_660_984);
    }

    #[test]
    fn sampling() {
        assert_eq!(uniform_int(0, 3, 7), 3);
        assert_eq!(uniform_int(u64::MAX, 3, 7), 7);
        let t = [(0, 10), (1 << 32, 20)];
        assert_eq!(sample_table(0, &t), 10);
        assert_eq!(sample_table(1 << 63, &t), 15);
        assert_eq!(sample_table(u64::MAX, &t), 19);
    }
}
