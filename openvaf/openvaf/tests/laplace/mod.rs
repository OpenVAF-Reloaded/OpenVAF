//! Enhancement-4: `laplace_*` filters, checked against the transfer functions of
//! LRM 4.5.11.
//!
//! Each test compiles a module `V(out) <+ laplace_xx(V(in), ...)`, evaluates it once in
//! the mock simulator and reads back the resistive (G) and reactive (C) Jacobians. The
//! filters are linear, so the small-signal response follows from solving
//! `(G + jwC) x = -(G + jwC)[:, in]` over all unknowns except `in`, which is driven
//! with 1. `x[out]` is then H(jw), compared with the analytic transfer function.

use std::ops::{Add, Div, Mul, Neg, Sub};

use camino::Utf8PathBuf;
use mini_harness::Result;

use crate::compile_and_load;
use crate::load::EvalFlags;

#[derive(Clone, Copy, Debug, PartialEq)]
struct C64 {
    re: f64,
    im: f64,
}

const fn c(re: f64, im: f64) -> C64 {
    C64 { re, im }
}

impl C64 {
    fn abs(self) -> f64 {
        self.re.hypot(self.im)
    }
}

impl Add for C64 {
    type Output = C64;
    fn add(self, o: C64) -> C64 {
        c(self.re + o.re, self.im + o.im)
    }
}

impl Sub for C64 {
    type Output = C64;
    fn sub(self, o: C64) -> C64 {
        c(self.re - o.re, self.im - o.im)
    }
}

impl Mul for C64 {
    type Output = C64;
    fn mul(self, o: C64) -> C64 {
        c(self.re * o.re - self.im * o.im, self.re * o.im + self.im * o.re)
    }
}

impl Div for C64 {
    type Output = C64;
    fn div(self, o: C64) -> C64 {
        let d = o.re * o.re + o.im * o.im;
        c((self.re * o.re + self.im * o.im) / d, (self.im * o.re - self.re * o.im) / d)
    }
}

impl Neg for C64 {
    type Output = C64;
    fn neg(self) -> C64 {
        c(-self.re, -self.im)
    }
}

/// Angular frequencies at which every filter is checked, DC included.
const OMEGAS: [f64; 5] = [0.0, 1e2, 1e3, 1e4, 1e5];

/// sum_k coeffs[k] * s^k
fn poly(coeffs: &[f64], s: C64) -> C64 {
    coeffs.iter().rev().fold(c(0.0, 0.0), |acc, &k| acc * s + c(k, 0.0))
}

/// LRM 4.5.11 root form: prod_k (1 - s/r_k), with the roots given as (re, im) pairs.
/// A root at the origin contributes the factor `s`.
fn root_poly(roots: &[f64], s: C64) -> C64 {
    roots.chunks(2).fold(c(1.0, 0.0), |acc, pair| {
        let r = c(pair[0], pair[1]);
        let factor = if r.abs() == 0.0 { s } else { c(1.0, 0.0) - s / r };
        acc * factor
    })
}

/// Solves the dense complex system `a x = b` by Gaussian elimination with partial
/// pivoting.
fn solve(mut a: Vec<Vec<C64>>, mut b: Vec<C64>) -> Vec<C64> {
    let n = b.len();
    for col in 0..n {
        let pivot = (col..n)
            .max_by(|&i, &j| a[i][col].abs().partial_cmp(&a[j][col].abs()).unwrap())
            .unwrap();
        assert!(a[pivot][col].abs() > 0.0, "singular small-signal system");
        a.swap(col, pivot);
        b.swap(col, pivot);
        for row in col + 1..n {
            let f = a[row][col] / a[col][col];
            for k in col..n {
                let v = a[col][k];
                a[row][k] = a[row][k] - f * v;
            }
            let v = b[col];
            b[row] = b[row] - f * v;
        }
    }
    let mut x = vec![c(0.0, 0.0); n];
    for row in (0..n).rev() {
        let sum = (row + 1..n).fold(b[row], |acc, k| acc - a[row][k] * x[k]);
        x[row] = sum / a[row][row];
    }
    x
}

/// Compiles a module with the given declarations and analog statement and returns
/// H(jw) = V(out)/V(in) for every w in `OMEGAS`.
fn simulate(name: &str, decls: &str, stmt: &str) -> Result<Vec<C64>> {
    let src = format!(
        "`include \"disciplines.vams\"\n\
         module {name}(in, out);\n\
         \x20   inout in, out;\n\
         \x20   electrical in, out;\n\
         \x20   {decls}\n\
         \x20   analog {stmt}\n\
         endmodule\n"
    );
    let root_file: Utf8PathBuf =
        Utf8PathBuf::try_from(std::env::temp_dir())?.join(format!("openvaf_laplace_{name}.va"));
    std::fs::write(&root_file, src)?;
    let desc = compile_and_load(&root_file);
    let model = desc.new_model();
    model.process_params()?;
    let mut instance = model.new_instance();
    let mut sim = instance.mock_simulation(&model, desc.num_terminals, 300.0)?;
    instance.eval(&model, &mut sim, EvalFlags::empty());
    instance.load_dae(&model, &mut sim);

    // unknowns: every node except ground and the driven input
    let input = sim.nodes.get_index_of("in").unwrap() as u32;
    let unknowns: Vec<u32> = (1..sim.nodes.len() as u32).filter(|&n| n != input).collect();
    let pos = |node: u32| unknowns.iter().position(|&u| u == node);
    let out = pos(sim.nodes.get_index_of("out").unwrap() as u32).unwrap();

    let mut res = Vec::new();
    for w in OMEGAS {
        let n = unknowns.len();
        let mut a = vec![vec![c(0.0, 0.0); n]; n];
        let mut b = vec![c(0.0, 0.0); n];
        for (i, &(row, col)) in sim.jacobian_info.iter().enumerate().skip(1) {
            let (g, cap) = unsafe {
                (sim.jacobian_resist[i].get().read(), sim.jacobian_react[i].get().read())
            };
            let y = c(g, w * cap);
            let Some(r) = pos(row) else { continue };
            if col == input {
                b[r] = b[r] - y;
            } else if let Some(k) = pos(col) {
                a[r][k] = a[r][k] + y;
            }
        }
        res.push(solve(a, b)[out]);
    }
    Ok(res)
}

/// Checks `V(out) <+ <filter>;` against the expected transfer function.
fn check(name: &str, filter: &str, expected: impl Fn(C64) -> C64) -> Result<()> {
    check_stmt(name, "", &format!("V(out) <+ {filter};"), expected)
}

fn check_stmt(name: &str, decls: &str, stmt: &str, expected: impl Fn(C64) -> C64) -> Result<()> {
    let h = simulate(name, decls, stmt)?;
    for (w, h) in OMEGAS.into_iter().zip(h) {
        let want = expected(c(0.0, w));
        let err = (h - want).abs() / want.abs();
        assert!(
            err < 1e-9,
            "{name}: H(j{w:e}) = {h:?}, expected {want:?} (relative error {err:e})"
        );
    }
    Ok(())
}

// laplace_nd: numerator and denominator coefficients
pub fn nd() -> Result<()> {
    check("lap_nd", "laplace_nd(V(in), '{2.0, 3.0}, '{1.0, 1e-3, 1e-7})", |s| {
        poly(&[2.0, 3.0], s) / poly(&[1.0, 1e-3, 1e-7], s)
    })
}

// Enhancement-4 part 3: array variables as coefficient vectors
pub fn nd_array_vars() -> Result<()> {
    check_stmt(
        "lap_nd_arr",
        "real [0:1] num; real [0:2] den;",
        "begin\n\
         \x20       num[0] = 2.0; num[1] = 3.0;\n\
         \x20       den[0] = 1.0; den[1] = 1e-3; den[2] = 1e-7;\n\
         \x20       V(out) <+ laplace_nd(V(in), num, den);\n\
         \x20   end",
        |s| poly(&[2.0, 3.0], s) / poly(&[1.0, 1e-3, 1e-7], s),
    )
}

// integer coefficients are converted to real (LRM 9.19)
#[allow(dead_code)] // disabled in integration.rs until fixed
pub fn nd_int_coeffs() -> Result<()> {
    check("lap_nd_int", "laplace_nd(V(in), '{1}, '{1, 1e-3})", |s| {
        c(1.0, 0.0) / poly(&[1.0, 1e-3], s)
    })
}

// laplace_zp: zeros and poles as (re, im) pairs, normalized to DC gain 1
#[allow(dead_code)] // disabled in integration.rs until fixed
pub fn zp_real() -> Result<()> {
    check("lap_zp", "laplace_zp(V(in), '{-1e4, 0.0}, '{-1e3, 0.0, -1e5, 0.0})", |s| {
        root_poly(&[-1e4, 0.0], s) / root_poly(&[-1e3, 0.0, -1e5, 0.0], s)
    })
}

// a complex-conjugate pole pair: (re, im) = (-1e3, +-2e3)
#[allow(dead_code)] // disabled in integration.rs until fixed
pub fn zp_complex() -> Result<()> {
    check("lap_zp_cplx", "laplace_zp(V(in), '{-1e5, 0.0}, '{-1e3, 2e3, -1e3, -2e3})", |s| {
        root_poly(&[-1e5, 0.0], s) / root_poly(&[-1e3, 2e3, -1e3, -2e3], s)
    })
}

// a zero at the origin contributes the factor s
#[allow(dead_code)] // disabled in integration.rs until fixed
pub fn zp_origin_zero() -> Result<()> {
    check("lap_zp_origin", "laplace_zp(V(in), '{0.0, 0.0}, '{-1e3, 0.0})", |s| {
        root_poly(&[0.0, 0.0], s) / root_poly(&[-1e3, 0.0], s)
    })
}

// laplace_np: numerator coefficients, denominator roots
#[allow(dead_code)] // disabled in integration.rs until fixed
pub fn np() -> Result<()> {
    check("lap_np", "laplace_np(V(in), '{1.0, 1e-4}, '{-1e3, 0.0})", |s| {
        poly(&[1.0, 1e-4], s) / root_poly(&[-1e3, 0.0], s)
    })
}

// laplace_zd: numerator roots, denominator coefficients
#[allow(dead_code)] // disabled in integration.rs until fixed
pub fn zd() -> Result<()> {
    check("lap_zd", "laplace_zd(V(in), '{-1e4, 0.0}, '{1.0, 1e-3})", |s| {
        root_poly(&[-1e4, 0.0], s) / poly(&[1.0, 1e-3], s)
    })
}

// integer literals in a root vector (the LRM's own examples are written like this)
#[allow(dead_code)] // disabled in integration.rs until fixed
pub fn zp_int_roots() -> Result<()> {
    check("lap_zp_int", "laplace_zp(V(in), '{-10000, 0}, '{-1000, 0})", |s| {
        root_poly(&[-1e4, 0.0], s) / root_poly(&[-1e3, 0.0], s)
    })
}

// LRM 4.5.11: the zeros argument may be a null argument
#[allow(dead_code)] // disabled in integration.rs until fixed
pub fn zp_null_zeros() -> Result<()> {
    check("lap_zp_null", "laplace_zp(V(in), , '{-1e3, 0.0})", |s| {
        c(1.0, 0.0) / root_poly(&[-1e3, 0.0], s)
    })
}
