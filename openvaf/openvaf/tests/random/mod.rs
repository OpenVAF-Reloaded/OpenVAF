//! `$random`/`$arandom`: generator sequences (checked against a reimplementation of
//! the stdlib generator) and the compile errors of illegal calls.

use camino::Utf8PathBuf;
use mini_harness::Result;

use crate::load::EvalFlags;
use crate::{compile_and_load_modules, compile_and_load_modules_with, compile_opts, compiles};

fn fmix32(mut h: u32) -> u32 {
    h ^= h >> 16;
    h = h.wrapping_mul(0x85eb_ca6b);
    h ^= h >> 13;
    h = h.wrapping_mul(0xc2b2_ae35);
    h ^= h >> 16;
    h
}

fn mix32(base: u32, site_id: u32) -> u32 {
    fmix32(base ^ fmix32(site_id.wrapping_add(0x9e37_79b9)))
}

/// Initial state of a generator seeded with the entity seed
fn site_seed(entity_seed: u32, site_id: u32) -> i32 {
    mix32(entity_seed, site_id) as i32
}

/// Next state of a generator
fn next(state: i32) -> i32 {
    69069u32.wrapping_mul(state as u32).wrapping_add(1) as i32
}

/// Random value of a generator state
fn value(state: i32) -> i32 {
    fmix32(state as u32) as i32
}

const SRC: &str = r#"`include "disciplines.vams"
module random_test(a, b, c, d, e, f, g, h, l);
    inout a, b, c, d, e, f, g, h, l;
    electrical a, b, c, d, e, f, g, h, l;
    parameter integer seed = 7;
    parameter integer p = $arandom(11);
    integer x = $arandom(13);
    integer s = 5;
    integer k, last;

    analog function integer rnd;
        input dummy;
        integer dummy;
        begin
            rnd = $random();
        end
    endfunction

    analog begin
        I(a) <+ $random();
        I(b) <+ $arandom(seed + 1);
        I(c) <+ $random(s);
        I(d) <+ p;
        I(e) <+ x;
        I(f) <+ $arandom(s, "global");
        I(g) <+ rnd(0);
        I(h) <+ rnd(1);
        for (k = 0; k < 10; k = k + 1)
            last = $arandom(17);
        I(l) <+ last;
    end
endmodule
"#;

/// With full Verilog-A (`-s`) `$random()`, `$arandom()` and `$arandom(constant)` keep
/// the generator state as hidden state, `$random(var)` in the variable. Each generator
/// advances once per executed call (10 times per evaluation in the loop), the advanced
/// state is kept only by an accepted evaluation. Generators without a seed are seeded with
/// the entity seed mixed with their site id (each inlined function call gets its own).
/// In initializers `$arandom(constant)` gives the first value of the sequence.
/// Typed calls return 0.
pub fn generators() -> Result<()> {
    if stdx::IS_CI && cfg!(windows) {
        return Ok(());
    }

    let tmp_dir = Utf8PathBuf::try_from(std::env::temp_dir())?;
    let root_file = tmp_dir.join("openvaf_random_test.va");
    std::fs::write(&root_file, SRC)?;
    let libs = compile_and_load_modules(&root_file, false);
    assert_eq!(libs.len(), 1);
    let desc = &libs[0];

    for entity_seed in [0, 12345, 0xdead_beef] {
        let model = desc.new_model();
        model.process_params()?;
        let mut instance = model.new_instance();
        instance.entity_seed = entity_seed;
        let mut sim = instance.mock_simulation(&model, desc.num_terminals, 300.0)?;

        // node, generator state, calls per evaluation (site ids: a 0, b 1, g 2, h 3, l 4)
        let mut states = [
            ("a", site_seed(entity_seed, 0), 1),
            ("b", 8, 1),
            ("c", 5, 1),
            ("g", site_seed(entity_seed, 2), 1),
            ("h", site_seed(entity_seed, 3), 1),
            ("l", 17, 10),
        ];
        let constants = [("d", value(next(11))), ("e", value(next(13))), ("f", 0)];

        for step in 1..=3 {
            let t = step as f64 * 1e-6;
            sim.abstime = t;
            sim.dt = 1e-6;
            for (_, state, calls) in &mut states {
                for _ in 0..*calls {
                    *state = next(*state);
                }
            }
            // without accept the generators do not advance
            for _ in 0..2 {
                sim.clear();
                instance.eval(&model, &mut sim, EvalFlags::ANALYSIS_TRAN);
                instance.load_dae(&model, &mut sim);
                for &(node, state, _) in &states {
                    let expected = value(state) as f64;
                    assert_eq!(sim.read_residual(node).0, expected, "{node} step {step}");
                }
                for &(node, expected) in &constants {
                    assert_eq!(sim.read_residual(node).0, expected as f64, "{node} step {step}");
                }
            }
            instance.accept(&model, t, 1e-6);
        }
    }
    Ok(())
}

/// One step of the IEEE 1364-2005 `$random` (`rtl_dist_uniform(seed, INT32_MIN, INT32_MAX)`),
/// returns the new seed and the value
fn ieee_random(seed: i32) -> (i32, i32) {
    let old = match seed as u32 {
        0 => 259_341_593,
        seed => seed,
    };
    let new = 69069u32.wrapping_mul(old).wrapping_add(1);
    // uniform(seed, INT32_MIN, INT32_MAX)
    let (a, b) = (i32::MIN as f64, i32::MAX as f64);
    let d = 0.00000011920928955078125;
    let c = 1.0 + (new >> 9) as f64 * 0.00000011920928955078125;
    let c = c + c * d;
    let u = (b - a) * (c - 1.0) + a;
    let r = (u + 2147483648.0) / 4294967295.0;
    let r = r * 4294967296.0 - 2147483648.0;
    let i = if r >= 0.0 { r as i64 } else { (r - 1.0) as i64 };
    (new as i32, i as u32 as i32)
}

/// `rtl_dist_uniform_alt`: uniform integer on `[lo, hi]` by rejection, returns the
/// new seed and the value
fn uniform_int(mut seed: i32, lo: i32, hi: i32) -> (i32, i32) {
    if lo >= hi {
        return (seed, lo);
    }
    let n = (hi as u32).wrapping_sub(lo as u32).wrapping_add(1);
    let thresh = 0u32.wrapping_sub(n) % n;
    loop {
        seed = next(seed);
        let m = value(seed) as u32 as u64 * n as u64;
        if m as u32 >= thresh {
            return (seed, (lo as u32).wrapping_add((m >> 32) as u32) as i32);
        }
    }
}

/// IEEE 1364-2005 `rtl_dist_uniform(seed, start, end)` for `end != INT32_MAX`,
/// returns the new seed and the value
fn ieee_uniform_int(seed: i32, start: i32, end: i32) -> (i32, i32) {
    if start >= end {
        return (seed, start);
    }
    let e = end as i64 + 1;
    let old = match seed as u32 {
        0 => 259_341_593,
        seed => seed,
    };
    let new = 69069u32.wrapping_mul(old).wrapping_add(1);
    // uniform(seed, start, e)
    let (a, b) = (start as f64, e as i32 as f64);
    let d = 0.00000011920928955078125;
    let c = 1.0 + (new >> 9) as f64 * 0.00000011920928955078125;
    let c = c + c * d;
    let r = (b - a) * (c - 1.0) + a;
    let mut i = if r >= 0.0 { r as i64 } else { (r - 1.0) as i64 };
    i = i.max(start as i64).min(e - 1);
    (new as i32, i as i32)
}

const DIST_UNIFORM_SRC: &str = r#"`include "disciplines.vams"
module dist_uniform_test(a, b, c);
    inout a, b, c;
    electrical a, b, c;
    integer s1 = 3, s2 = 0, s3 = 9;
    analog begin
        I(a) <+ $dist_uniform(s1, -5, 7);
        I(b) <+ $dist_uniform(s2, 0, 1);
        // start >= end returns start without advancing the seed
        I(c) <+ $dist_uniform(s3, 4, 4) + $dist_uniform(s3, -3, 100);
    end
endmodule
"#;

/// `$dist_uniform(var, start, end)` advances the seed variable once per call and
/// returns a uniform integer on `[start, end]`, with both generators.
pub fn dist_uniform() -> Result<()> {
    if stdx::IS_CI && cfg!(windows) {
        return Ok(());
    }

    let tmp_dir = Utf8PathBuf::try_from(std::env::temp_dir())?;
    for ieee in [false, true] {
        let gen = if ieee { ieee_uniform_int } else { uniform_int };
        let root_file = tmp_dir.join(format!("openvaf_dist_uniform_{ieee}.va"));
        std::fs::write(&root_file, DIST_UNIFORM_SRC)?;
        let mut opts = compile_opts(&root_file, false);
        opts.ieee1364 = ieee;
        let libs = compile_and_load_modules_with(&opts);
        assert_eq!(libs.len(), 1);
        let desc = &libs[0];
        let model = desc.new_model();
        model.process_params()?;
        let mut instance = model.new_instance();
        let mut sim = instance.mock_simulation(&model, desc.num_terminals, 300.0)?;

        let (mut s1, mut s2, mut s3) = (3, 0, 9);
        for step in 1..=20 {
            let t = step as f64 * 1e-6;
            sim.abstime = t;
            sim.dt = 1e-6;
            sim.clear();
            instance.eval(&model, &mut sim, EvalFlags::ANALYSIS_TRAN);
            instance.load_dae(&model, &mut sim);

            let (next, a) = gen(s1, -5, 7);
            s1 = next;
            assert!((-5..=7).contains(&a));
            assert_eq!(sim.read_residual("a").0, a as f64, "ieee {ieee} a step {step}");
            let (next, b) = gen(s2, 0, 1);
            s2 = next;
            assert_eq!(sim.read_residual("b").0, b as f64, "ieee {ieee} b step {step}");
            let (next, c1) = gen(s3, 4, 4);
            assert_eq!(c1, 4);
            assert_eq!(next, s3);
            let (next, c2) = gen(next, -3, 100);
            s3 = next;
            assert_eq!(sim.read_residual("c").0, (c1 + c2) as f64, "ieee {ieee} c step {step}");
            instance.accept(&model, t, 1e-6);
        }
    }
    Ok(())
}

/// IEEE 1364-2005 `uniform(seed, start, end)`, returns the new seed and the value
fn ieee_uniform(seed: i32, start: i32, end: i32) -> (i32, f64) {
    let old = match seed as u32 {
        0 => 259_341_593,
        seed => seed,
    };
    let (a, b) = if start >= end { (0.0, 2147483647.0) } else { (start as f64, end as f64) };
    let new = 69069u32.wrapping_mul(old).wrapping_add(1);
    let d = 0.00000011920928955078125;
    let c = 1.0 + (new >> 9) as f64 * 0.00000011920928955078125;
    let c = c + c * d;
    (new as i32, (b - a) * (c - 1.0) + a)
}

/// `uniform_alt(seed, a, b)`, returns the new seed and the value
fn uniform_alt(seed: i32, a: f64, b: f64) -> (i32, f64) {
    let seed = next(seed);
    let u = (value(seed) as u32 as f64 + 0.5) * 2f64.powi(-32);
    (seed, a * (1.0 - u) + b * u)
}

/// Polar method of `normal`/`normal_alt` on a uniform generator on `(-1, 1)`,
/// returns the new seed and the value
fn polar(mut seed: i32, mean: f64, sd: f64, uniform: fn(i32) -> (i32, f64)) -> (i32, f64) {
    let (mut v1, mut s) = (0.0, 1.0);
    while s >= 1.0 || s == 0.0 {
        let (next, u1) = uniform(seed);
        let (next, u2) = uniform(next);
        seed = next;
        v1 = u1;
        s = u1 * u1 + u2 * u2;
    }
    (seed, v1 * (-2.0 * s.ln() / s).sqrt() * sd + mean)
}

/// `rtl_dist_normal_alt`, returns the new seed and the value
fn normal_int(seed: i32, mean: i32, sd: i32) -> (i32, i32) {
    let (seed, r) = polar(seed, mean as f64, sd as f64, |s| uniform_alt(s, -1.0, 1.0));
    // `as` saturates like the C code
    (seed, r.round() as i32)
}

/// IEEE 1364-2005 `rtl_dist_normal`, returns the new seed and the value
fn ieee_normal_int(seed: i32, mean: i32, sd: i32) -> (i32, i32) {
    let (seed, r) = polar(seed, mean as f64, sd as f64, |s| ieee_uniform(s, -1, 1));
    let i = if r >= 0.0 { (r + 0.5) as i32 } else { -((-r + 0.5) as i32) };
    (seed, i)
}

const DIST_NORMAL_SRC: &str = r#"`include "disciplines.vams"
module dist_normal_test(a, b, c);
    inout a, b, c;
    electrical a, b, c;
    integer s1 = 3, s2 = 0, s3 = 9;
    analog begin
        I(a) <+ $dist_normal(s1, 10, 3);
        I(b) <+ $dist_normal(s2, -100, 1000);
        // a zero standard deviation returns the mean, but advances the seed
        I(c) <+ $dist_normal(s3, 4, 0) + $dist_normal(s3, 0, 5);
    end
endmodule
"#;

/// `$dist_normal(var, mean, sd)` advances the seed variable on each call and
/// returns a normally distributed integer, with both generators.
pub fn dist_normal() -> Result<()> {
    if stdx::IS_CI && cfg!(windows) {
        return Ok(());
    }

    let tmp_dir = Utf8PathBuf::try_from(std::env::temp_dir())?;
    for ieee in [false, true] {
        let gen = if ieee { ieee_normal_int } else { normal_int };
        let root_file = tmp_dir.join(format!("openvaf_dist_normal_{ieee}.va"));
        std::fs::write(&root_file, DIST_NORMAL_SRC)?;
        let mut opts = compile_opts(&root_file, false);
        opts.ieee1364 = ieee;
        let libs = compile_and_load_modules_with(&opts);
        assert_eq!(libs.len(), 1);
        let desc = &libs[0];
        let model = desc.new_model();
        model.process_params()?;
        let mut instance = model.new_instance();
        let mut sim = instance.mock_simulation(&model, desc.num_terminals, 300.0)?;

        let (mut s1, mut s2, mut s3) = (3, 0, 9);
        for step in 1..=20 {
            let t = step as f64 * 1e-6;
            sim.abstime = t;
            sim.dt = 1e-6;
            sim.clear();
            instance.eval(&model, &mut sim, EvalFlags::ANALYSIS_TRAN);
            instance.load_dae(&model, &mut sim);

            let (next, a) = gen(s1, 10, 3);
            s1 = next;
            assert_eq!(sim.read_residual("a").0, a as f64, "ieee {ieee} a step {step}");
            let (next, b) = gen(s2, -100, 1000);
            s2 = next;
            assert_eq!(sim.read_residual("b").0, b as f64, "ieee {ieee} b step {step}");
            let (next, c1) = gen(s3, 4, 0);
            assert_eq!(c1, 4);
            assert_ne!(next, s3);
            let (next, c2) = gen(next, 0, 5);
            s3 = next;
            assert_eq!(sim.read_residual("c").0, (c1 + c2) as f64, "ieee {ieee} c step {step}");
            instance.accept(&model, t, 1e-6);
        }
    }
    Ok(())
}

extern "C" {
    fn lgamma(x: f64) -> f64;
}

/// Uniform and normal generators of the alternative (`ieee == false`) or the IEEE
/// 1364-2005 stdlib generators, on a seed that is advanced in place
#[derive(Clone, Copy)]
struct Gen {
    ieee: bool,
}

impl Gen {
    /// `uniform(seed, a, b)` or `uniform_alt(seed, a, b)`
    fn uniform(self, seed: &mut i32, a: i32, b: i32) -> f64 {
        let (next, u) = if self.ieee {
            ieee_uniform(*seed, a, b)
        } else {
            uniform_alt(*seed, a as f64, b as f64)
        };
        *seed = next;
        u
    }

    /// `uniform(seed, 0, 1)` or `uniform_alt(seed, 0, 1)`
    fn unit(self, seed: &mut i32) -> f64 {
        self.uniform(seed, 0, 1)
    }

    /// `normal(seed, 0, 1)` or `normal_alt(seed, 0, 1)`
    fn std_normal(self, seed: &mut i32) -> f64 {
        let (next, r) = if self.ieee {
            polar(*seed, 0.0, 1.0, |s| ieee_uniform(s, -1, 1))
        } else {
            polar(*seed, 0.0, 1.0, |s| uniform_alt(s, -1.0, 1.0))
        };
        *seed = next;
        r
    }

    /// `exponential` or `exponential_alt`
    fn exponential(self, seed: &mut i32, mean: i32) -> f64 {
        let n = self.unit(seed);
        if n != 0.0 {
            -n.ln() * mean as f64
        } else {
            n
        }
    }

    /// Rounding of the `rtl_dist_*` functions (half away from zero)
    fn round(self, r: f64) -> i32 {
        if self.ieee {
            if r >= 0.0 {
                (r + 0.5) as i32
            } else {
                -((-r + 0.5) as i32)
            }
        } else {
            // `as` saturates like the C code
            r.round() as i32
        }
    }

    /// `poisson` or `poisson_alt`
    fn poisson(self, seed: &mut i32, mean: i32) -> i32 {
        if self.ieee {
            let mut n = 0;
            let p = (-(mean as f64)).exp();
            let mut q = self.unit(seed);
            while p < q {
                n += 1;
                q = self.unit(seed) * q;
            }
            return n;
        }
        let mean = mean as f64;
        if mean < 10.0 {
            let u = self.unit(seed);
            let mut p = (-mean).exp();
            let mut f = p;
            let mut k = 0;
            while u > f && p > 0.0 {
                k += 1;
                p *= mean / k as f64;
                f += p;
            }
            return k;
        }
        let slam = mean.sqrt();
        let loglam = mean.ln();
        let b = 0.931 + 2.53 * slam;
        let a = -0.059 + 0.02483 * b;
        let invalpha = 1.1239 + 1.1328 / (b - 3.4);
        let vr = 0.9277 - 3.6224 / (b - 2.0);
        loop {
            let u = self.unit(seed) - 0.5;
            let v = self.unit(seed);
            let us = 0.5 - u.abs();
            let k = ((2.0 * a / us + b) * u + mean + 0.43).floor();
            if us >= 0.07 && v <= vr {
                return k as i32;
            }
            if k < 0.0 || (us < 0.013 && v > us) {
                continue;
            }
            // SAFETY: lgamma from libm, as called by stdlib.c
            let lg = unsafe { lgamma(k + 1.0) };
            if v.ln() + invalpha.ln() - (a / (us * us) + b).ln() <= -mean + k * loglam - lg {
                return k as i32;
            }
        }
    }

    /// `gamma_alt`
    fn gamma(self, seed: &mut i32, shape: f64) -> f64 {
        let d = shape - 1.0 / 3.0;
        let c = 1.0 / (9.0 * d).sqrt();
        loop {
            let (mut x, mut v);
            loop {
                x = self.std_normal(seed);
                v = 1.0 + c * x;
                if v > 0.0 {
                    break;
                }
            }
            v = v * v * v;
            let u = self.unit(seed);
            let x2 = x * x;
            if u < 1.0 - 0.0331 * x2 * x2 {
                return d * v;
            }
            if u.ln() < 0.5 * x2 + d * (1.0 - v + v.ln()) {
                return d * v;
            }
        }
    }

    /// `chi_square` or `chi_square_alt`
    fn chi_square(self, seed: &mut i32, df: i32) -> f64 {
        if self.ieee {
            let mut x = if df % 2 != 0 {
                let x = self.std_normal(seed);
                x * x
            } else {
                0.0
            };
            for _ in (2..=df).step_by(2) {
                x = x + 2.0 * self.exponential(seed, 1);
            }
            return x;
        }
        if df == 1 {
            let z = self.std_normal(seed);
            return z * z;
        }
        2.0 * self.gamma(seed, 0.5 * df as f64)
    }

    /// `t` or `t_alt`
    fn t(self, seed: &mut i32, df: i32) -> f64 {
        if self.ieee {
            let chi2 = self.chi_square(seed, df);
            let root = (chi2 / df as f64).sqrt();
            return self.std_normal(seed) / root;
        }
        let n = df as f64;
        let (u, w) = loop {
            let u = self.uniform(seed, -1, 1);
            let v = self.uniform(seed, -1, 1);
            let w = u * u + v * v;
            if w < 1.0 {
                break (u, w);
            }
        };
        u * (n * (-2.0 * w.ln() / n).exp_m1() / w).sqrt()
    }

    /// `erlangian` or `erlang_alt`
    fn erlang(self, seed: &mut i32, k: i32, mean: i32) -> f64 {
        let (mean, kf) = (mean as f64, k as f64);
        if self.ieee {
            let mut x = 1.0;
            for _ in 0..k {
                x = x * self.unit(seed);
            }
            return -mean * x.ln() / kf;
        }
        let g = if k <= 3 {
            let mut x = self.unit(seed);
            for _ in 1..k {
                x *= self.unit(seed);
            }
            -x.ln()
        } else {
            self.gamma(seed, kf)
        };
        g * mean / kf
    }

    /// `$dist_exponential(seed, mean)`
    fn dist_exponential(self, seed: &mut i32, mean: i32) -> i32 {
        if mean <= 0 {
            return 0;
        }
        let r = self.exponential(seed, mean);
        self.round(r)
    }

    /// `$dist_poisson(seed, mean)`
    fn dist_poisson(self, seed: &mut i32, mean: i32) -> i32 {
        if mean <= 0 {
            return 0;
        }
        self.poisson(seed, mean)
    }

    /// `$dist_chi_square(seed, df)`
    fn dist_chi_square(self, seed: &mut i32, df: i32) -> i32 {
        if df <= 0 {
            return 0;
        }
        let r = self.chi_square(seed, df);
        self.round(r)
    }

    /// `$dist_t(seed, df)`
    fn dist_t(self, seed: &mut i32, df: i32) -> i32 {
        if df <= 0 {
            return 0;
        }
        let r = self.t(seed, df);
        self.round(r)
    }

    /// `$dist_erlang(seed, k, mean)`
    fn dist_erlang(self, seed: &mut i32, k: i32, mean: i32) -> i32 {
        if k <= 0 {
            return 0;
        }
        let r = self.erlang(seed, k, mean);
        self.round(r)
    }
}

const DIST_OTHER_SRC: &str = r#"`include "disciplines.vams"
module dist_other_test(a, b, c, d, e, f, g, h, l, m);
    inout a, b, c, d, e, f, g, h, l, m;
    electrical a, b, c, d, e, f, g, h, l, m;
    integer s1 = 1, s2 = 2, s3 = 3, s4 = 4, s5 = 5, s6 = 6, s7 = 7, s8 = 8, s9 = 9, s10 = 0;
    analog begin
        I(a) <+ $dist_exponential(s1, 10);
        // invalid mean returns 0 without advancing the seed
        I(b) <+ $dist_poisson(s2, 0) + $dist_poisson(s2, 3);
        I(c) <+ $dist_poisson(s3, 50);
        I(d) <+ $dist_chi_square(s4, 1);
        I(e) <+ $dist_chi_square(s5, 5);
        I(f) <+ $dist_chi_square(s6, 4);
        I(g) <+ $dist_t(s7, 3);
        I(h) <+ $dist_erlang(s8, 2, 10);
        I(l) <+ $dist_erlang(s9, 5, -10);
        // invalid arguments return 0 without advancing the seed
        I(m) <+ $dist_exponential(s10, 0) + $dist_chi_square(s10, -1) + $dist_t(s10, 0)
            + $dist_erlang(s10, 0, 5) + $dist_exponential(s10, 7);
    end
endmodule
"#;

/// `$dist_exponential`, `$dist_poisson`, `$dist_chi_square`, `$dist_t` and
/// `$dist_erlang` advance the seed variable and return the values of the reference
/// implementation, with both generators.
pub fn dist_other() -> Result<()> {
    if stdx::IS_CI && cfg!(windows) {
        return Ok(());
    }

    let tmp_dir = Utf8PathBuf::try_from(std::env::temp_dir())?;
    for ieee in [false, true] {
        let gen = Gen { ieee };
        let root_file = tmp_dir.join(format!("openvaf_dist_other_{ieee}.va"));
        std::fs::write(&root_file, DIST_OTHER_SRC)?;
        let mut opts = compile_opts(&root_file, false);
        opts.ieee1364 = ieee;
        let libs = compile_and_load_modules_with(&opts);
        assert_eq!(libs.len(), 1);
        let desc = &libs[0];
        let model = desc.new_model();
        model.process_params()?;
        let mut instance = model.new_instance();
        let mut sim = instance.mock_simulation(&model, desc.num_terminals, 300.0)?;

        let mut s = [1, 2, 3, 4, 5, 6, 7, 8, 9, 0];
        for step in 1..=20 {
            let t = step as f64 * 1e-6;
            sim.abstime = t;
            sim.dt = 1e-6;
            sim.clear();
            instance.eval(&model, &mut sim, EvalFlags::ANALYSIS_TRAN);
            instance.load_dae(&model, &mut sim);

            let old = s[1];
            let b0 = gen.dist_poisson(&mut s[1], 0);
            assert_eq!((b0, s[1]), (0, old));
            let old = s[9];
            let m0 = gen.dist_exponential(&mut s[9], 0)
                + gen.dist_chi_square(&mut s[9], -1)
                + gen.dist_t(&mut s[9], 0)
                + gen.dist_erlang(&mut s[9], 0, 5);
            assert_eq!((m0, s[9]), (0, old));
            let expected = [
                ("a", gen.dist_exponential(&mut s[0], 10)),
                ("b", gen.dist_poisson(&mut s[1], 3)),
                ("c", gen.dist_poisson(&mut s[2], 50)),
                ("d", gen.dist_chi_square(&mut s[3], 1)),
                ("e", gen.dist_chi_square(&mut s[4], 5)),
                ("f", gen.dist_chi_square(&mut s[5], 4)),
                ("g", gen.dist_t(&mut s[6], 3)),
                ("h", gen.dist_erlang(&mut s[7], 2, 10)),
                ("l", gen.dist_erlang(&mut s[8], 5, -10)),
                ("m", gen.dist_exponential(&mut s[9], 7)),
            ];
            for (node, value) in expected {
                assert_eq!(
                    sim.read_residual(node).0,
                    value as f64,
                    "ieee {ieee} {node} step {step}"
                );
            }
            instance.accept(&model, t, 1e-6);
        }
    }
    Ok(())
}

/// With `--ieee1364` `$random(var)` and `$arandom(constant)` use the IEEE 1364-2005
/// generator.
pub fn ieee1364() -> Result<()> {
    if stdx::IS_CI && cfg!(windows) {
        return Ok(());
    }

    const SRC: &str = r#"`include "disciplines.vams"
module random_ieee(a, b);
    inout a, b;
    electrical a, b;
    integer s = 0;
    analog begin
        I(a) <+ $random(s);
        I(b) <+ $arandom(5);
    end
endmodule
"#;
    let tmp_dir = Utf8PathBuf::try_from(std::env::temp_dir())?;
    let root_file = tmp_dir.join("openvaf_random_ieee_test.va");
    std::fs::write(&root_file, SRC)?;
    let mut opts = compile_opts(&root_file, false);
    opts.ieee1364 = true;
    let libs = compile_and_load_modules_with(&opts);
    assert_eq!(libs.len(), 1);
    let desc = &libs[0];
    let model = desc.new_model();
    model.process_params()?;
    let mut instance = model.new_instance();
    let mut sim = instance.mock_simulation(&model, desc.num_terminals, 300.0)?;

    let mut states = [("a", 0), ("b", 5)];
    for step in 1..=3 {
        let t = step as f64 * 1e-6;
        sim.abstime = t;
        sim.dt = 1e-6;
        sim.clear();
        instance.eval(&model, &mut sim, EvalFlags::ANALYSIS_TRAN);
        instance.load_dae(&model, &mut sim);
        for (node, state) in &mut states {
            let (next, value) = ieee_random(*state);
            assert_eq!(sim.read_residual(node).0, value as f64, "{node} step {step}");
            *state = next;
        }
        instance.accept(&model, t, 1e-6);
    }
    Ok(())
}

/// A voltage contribution that is zero after optimization but not a literal zero (a
/// typed `$arandom`, `1 - 1`) has no collapse hint. It keeps its branch equation
/// `V = 0` with the branch current as unknown.
pub fn zero_voltage() -> Result<()> {
    if stdx::IS_CI && cfg!(windows) {
        return Ok(());
    }

    const SRC: &str = r#"`include "disciplines.vams"
module zero_voltage(d, e);
    output d, e;
    electrical d, e;
    analog begin
        V(d) <+ $arandom(12345, "instance");
        V(e) <+ 1 - 1;
    end
endmodule
"#;
    let tmp_dir = Utf8PathBuf::try_from(std::env::temp_dir())?;
    let root_file = tmp_dir.join("openvaf_random_zero_voltage_test.va");
    std::fs::write(&root_file, SRC)?;
    let libs = compile_and_load_modules(&root_file, true);
    assert_eq!(libs.len(), 1);
    let desc = &libs[0];
    let model = desc.new_model();
    model.process_params()?;
    let mut instance = model.new_instance();
    let mut sim = instance.mock_simulation(&model, desc.num_terminals, 300.0)?;

    for (node, v) in [("d", 0.3), ("e", 0.2)] {
        sim.set_voltage(node, v);
    }
    instance.eval(&model, &mut sim, EvalFlags::empty());
    instance.load_dae(&model, &mut sim);
    for (node, v) in [("d", 0.3), ("e", 0.2)] {
        let flow = format!("flow({node})");
        // branch equation: 0 - V(node)
        assert_eq!(sim.read_residual(&flow), (-v, 0.0), "{node}");
        assert_eq!(sim.read_jacobian(&flow, node), (-1.0, 0.0), "{node}");
        // KCL: the branch current flows out of the node
        assert_eq!(sim.read_jacobian(node, &flow), (1.0, 0.0), "{node}");
    }
    Ok(())
}

fn module(name: &str, decls: &str, initial: &str, analog: &str) -> String {
    format!(
        r#"`include "disciplines.vams"
module {name}(a);
    inout a;
    electrical a;
    parameter integer seed = 7;
    integer s = 1;
    real r = 1.0;
{decls}
    analog initial begin
{initial}
    end

    analog begin
{analog}
    end
endmodule
"#
    )
}

/// Illegal calls are compile errors. Without `-s` only typed calls are allowed.
pub fn errors() -> Result<()> {
    if stdx::IS_CI && cfg!(windows) {
        return Ok(());
    }

    const RND: &str = "
    analog function integer rnd;
        input dummy;
        integer dummy;
        begin
            rnd = $random();
        end
    endfunction
";
    const RND_X: &str = "
    analog function integer rnd;
        input dummy;
        integer dummy;
        begin
            rnd = $random();
        end
    endfunction
    integer x = rnd(0);
";

    // (decls, analog initial, analog, compiles without -s, compiles with -s)
    let cases = [
        ("", "", "I(a) <+ $random();", false, true),
        ("", "", "I(a) <+ $random(s);", false, true),
        ("", "", "I(a) <+ $arandom(seed);", false, true),
        ("", "", "I(a) <+ $arandom(s, \"instance\");", true, true),
        ("", "s = $arandom(3, \"global\");", "I(a) <+ s;", true, true),
        ("", "", "I(a) <+ $arandom(1, \"local\");", false, false),
        ("", "", "I(a) <+ $arandom(r);", false, false),
        ("", "s = $random(s);", "I(a) <+ s;", false, false),
        (RND, "", "I(a) <+ rnd(0);", false, true),
        (RND, "s = rnd(0);", "I(a) <+ s;", false, false),
        ("parameter integer p = $arandom(seed);", "", "I(a) <+ p;", false, true),
        ("parameter integer p = $arandom(seed, \"global\");", "", "I(a) <+ p;", true, true),
        ("parameter integer p = $arandom();", "", "I(a) <+ p;", false, false),
        ("integer x = $arandom(seed * 2);", "", "I(a) <+ x;", false, true),
        ("integer x = $arandom();", "", "I(a) <+ x;", false, false),
        (RND_X, "", "I(a) <+ x;", false, false),
        ("", "", "I(a) <+ $dist_uniform(s, 0, 3);", false, true),
        ("", "", "I(a) <+ $dist_uniform(seed, 0, 3);", false, false),
        ("", "s = $dist_uniform(s, 0, 3);", "I(a) <+ s;", false, false),
        ("integer x = $dist_uniform(s, 0, 3);", "", "I(a) <+ x;", false, false),
        ("parameter integer p = $dist_uniform(seed, 0, 3);", "", "I(a) <+ p;", false, false),
        ("", "", "I(a) <+ $dist_normal(s, 0, 3);", false, true),
        ("", "", "I(a) <+ $dist_normal(seed, 0, 3);", false, false),
        ("", "s = $dist_normal(s, 0, 3);", "I(a) <+ s;", false, false),
        ("integer x = $dist_normal(s, 0, 3);", "", "I(a) <+ x;", false, false),
        ("parameter integer p = $dist_normal(seed, 0, 3);", "", "I(a) <+ p;", false, false),
        ("", "", "I(a) <+ $dist_exponential(s, 3);", false, true),
        ("", "", "I(a) <+ $dist_exponential(seed, 3);", false, false),
        ("", "", "I(a) <+ $dist_poisson(s, 3);", false, true),
        ("", "", "I(a) <+ $dist_poisson(seed, 3);", false, false),
        ("", "", "I(a) <+ $dist_chi_square(s, 3);", false, true),
        ("", "", "I(a) <+ $dist_chi_square(seed, 3);", false, false),
        ("", "", "I(a) <+ $dist_t(s, 3);", false, true),
        ("", "", "I(a) <+ $dist_t(seed, 3);", false, false),
        ("", "", "I(a) <+ $dist_erlang(s, 2, 3);", false, true),
        ("", "", "I(a) <+ $dist_erlang(seed, 2, 3);", false, false),
        ("", "s = $dist_erlang(s, 2, 3);", "I(a) <+ s;", false, false),
        ("integer x = $dist_t(s, 3);", "", "I(a) <+ x;", false, false),
        ("parameter integer p = $dist_poisson(seed, 3);", "", "I(a) <+ p;", false, false),
    ];

    let tmp_dir = Utf8PathBuf::try_from(std::env::temp_dir())?;
    for (i, (decls, initial, analog, compact_ok, full_ok)) in cases.into_iter().enumerate() {
        let name = format!("random_errors_{i}");
        let root_file = tmp_dir.join(format!("openvaf_{name}.va"));
        std::fs::write(&root_file, module(&name, decls, initial, analog))?;
        assert_eq!(
            compiles(&root_file, true),
            compact_ok,
            "case {i} without -s: {decls} {initial} {analog}"
        );
        assert_eq!(
            compiles(&root_file, false),
            full_ok,
            "case {i} with -s: {decls} {initial} {analog}"
        );
    }
    Ok(())
}
