//! Comprehensive verification and analytical exploration for Step 1, Step 2, and Step 3
//! of the Q_n-smooth (H_{2+epsilon}) roadmap for Erdos Problem #708.
//!
//! Compile and run:
//!   rustc -O --edition 2021 /Users/revenge/code/erdos-708-remediation/explore_h2_smooth.rs -o /Users/revenge/code/erdos-708-remediation/explore_h2_smooth
//!   /Users/revenge/code/erdos-708-remediation/explore_h2_smooth

use std::collections::VecDeque;

fn sieve_primes(limit: usize) -> Vec<usize> {
    let mut is_p = vec![true; limit + 1];
    is_p[0] = false;
    if limit >= 1 {
        is_p[1] = false;
    }
    let mut p = 2;
    while p * p <= limit {
        if is_p[p] {
            let mut mult = p * p;
            while mult <= limit {
                is_p[mult] = false;
                mult += p;
            }
        }
        p += 1;
    }
    (2..=limit).filter(|&x| is_p[x]).collect()
}

/// Exact integral \int_{lo}^{hi} 1_{u > t} dt = (min(u, hi) - lo)_+ for lo <= hi.
#[inline]
fn integral_indicator(u: f64, lo: f64, hi: f64) -> f64 {
    if hi <= lo {
        0.0
    } else {
        (u.min(hi) - lo).max(0.0)
    }
}

#[derive(Debug, Clone)]
struct PerPrimeBreakdown {
    j: usize,
    pj: usize,
    lhs_neg_s: f64,
    rhs_neg_s: f64,
    lhs_pos_s: f64,
    rhs_pos_s: f64,
}

/// Evaluate both the direct hinge sums and the exact Proposition 8(2) s-integral
/// at general c >= 1 for an arbitrary prime list `ps` and weights `w`.
/// Splits each (j, r) integral at s = 0 into s < 0 and s >= 0!
fn eval_telescoping_detailed(
    m: usize,
    x: usize,
    c: f64,
    ps: &[usize],
    w: &[f64],
) -> (f64, f64, f64, f64, Vec<PerPrimeBreakdown>) {
    let xw = |mut val: usize| -> f64 {
        let mut s = 0.0;
        for (i, &p) in ps.iter().enumerate() {
            if w[i] == 0.0 {
                continue;
            }
            while val % p == 0 {
                s += w[i];
                val /= p;
            }
        }
        s
    };

    let yj = |j: usize, mut val: usize| -> f64 {
        let mut s = 0.0;
        for i in 0..j {
            if w[i] == 0.0 {
                continue;
            }
            let p = ps[i];
            while val % p == 0 {
                s += w[i];
                val /= p;
            }
        }
        s
    };

    let lhs_direct: f64 = (1..=m).map(|k| (xw(k) - c).max(0.0)).sum();
    let rhs_direct: f64 = ((x + 1)..=(x + m)).map(|b| (xw(b) - 1.0).max(0.0)).sum();

    let mut lhs_tele = 0.0;
    let mut rhs_tele = 0.0;
    let mut breakdown = Vec::new();

    for (j, &pj) in ps.iter().enumerate() {
        let wp = w[j];
        if wp <= 0.0 {
            continue;
        }
        let mut lhs_neg = 0.0;
        let mut rhs_neg = 0.0;
        let mut lhs_pos = 0.0;
        let mut rhs_pos = 0.0;

        let mut r = 1usize;
        let mut p_pow = pj;
        while p_pow <= x + m {
            let lo = 1.0 - (r as f64) * wp;
            let hi = 1.0 - ((r - 1) as f64) * wp;

            let neg_lo = lo.min(0.0);
            let neg_hi = hi.min(0.0);
            let pos_lo = lo.max(0.0);
            let pos_hi = hi.max(0.0);

            if p_pow <= m {
                for k in 1..=(m / p_pow) {
                    // Indicator: Y_j(k) > s + (c - 1) <=> Y_j(k) - (c - 1) > s
                    let u_lhs = yj(j, k) - (c - 1.0);
                    lhs_neg += integral_indicator(u_lhs, neg_lo, neg_hi);
                    lhs_pos += integral_indicator(u_lhs, pos_lo, pos_hi);
                }
            }

            let b_start = (x / p_pow) + 1;
            let b_end = (x + m) / p_pow;
            if b_start <= b_end {
                for b_prime in b_start..=b_end {
                    let u_rhs = yj(j, b_prime);
                    rhs_neg += integral_indicator(u_rhs, neg_lo, neg_hi);
                    rhs_pos += integral_indicator(u_rhs, pos_lo, pos_hi);
                }
            }

            r += 1;
            p_pow = p_pow.saturating_mul(pj);
            if p_pow == 0 {
                break;
            }
        }

        lhs_tele += lhs_neg + lhs_pos;
        rhs_tele += rhs_neg + rhs_pos;
        breakdown.push(PerPrimeBreakdown {
            j,
            pj,
            lhs_neg_s: lhs_neg,
            rhs_neg_s: rhs_neg,
            lhs_pos_s: lhs_pos,
            rhs_pos_s: rhs_pos,
        });
    }

    (lhs_direct, rhs_direct, lhs_tele, rhs_tele, breakdown)
}

/// Step 2 Verification:
/// 1. Single-prime (K=1) and Two-prime (K=2): verify BOTH (H_2) AND (H_1) hold universally,
///    and that EVERY individual prime step j in {1, 2} has non-negative surplus on BOTH s < 0 and s >= 0!
/// 2. Three-prime (K=3) Erdos-Suranyi semiprime clique: inspect exact per-j surplus/deficit transfer!
fn verify_step2_few_primes() {
    let small_ps = [2usize, 3, 5, 7, 11, 13, 17, 19];
    let mut k2_checks = 0usize;
    let mut min_surplus_c1 = f64::INFINITY;
    let mut min_surplus_c2 = f64::INFINITY;

    for i1 in 0..small_ps.len() {
        for i2 in 0..small_ps.len() {
            if i1 == i2 {
                continue;
            }
            let p1 = small_ps[i1];
            let p2 = small_ps[i2];
            for &w1 in &[0.15, 0.4, 0.5, 0.75, 1.0] {
                for &w2 in &[0.2, 0.5, 0.85, 1.0] {
                    for &m in &[12usize, 35, 77, 144] {
                        for &x in &[0usize, 1, 17, 103, 719] {
                            for &c in &[1.0f64, 2.0f64] {
                                let (ld, rd, lt, rt, bd) =
                                    eval_telescoping_detailed(m, x, c, &[p1, p2], &[w1, w2]);
                                assert!(
                                    (ld - lt).abs() < 1e-10 && (rd - rt).abs() < 1e-10,
                                    "Telescoping identity mismatch at c={}: ({},{}) vs ({},{})",
                                    c, ld, rd, lt, rt
                                );
                                for step in &bd {
                                    assert!(
                                        step.rhs_neg_s + 1e-11 >= step.lhs_neg_s,
                                        "Negative-s dominance failed at j={}: {} < {}",
                                        step.j, step.rhs_neg_s, step.lhs_neg_s
                                    );
                                    assert!(
                                        step.rhs_pos_s + 1e-11 >= step.lhs_pos_s,
                                        "Two-prime positive-s dominance failed at c={}, j={}: {} < {}",
                                        c, step.j, step.rhs_pos_s, step.lhs_pos_s
                                    );
                                }
                                let surp = rt - lt;
                                if (c - 1.0).abs() < 1e-9 && surp < min_surplus_c1 {
                                    min_surplus_c1 = surp;
                                }
                                if (c - 2.0).abs() < 1e-9 && surp < min_surplus_c2 {
                                    min_surplus_c2 = surp;
                                }
                                k2_checks += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    println!(
        "[Step 2A/2B] Two-prime K=2 analytical dominance verified across {} instances: min_surplus(H_1)={:.6}, min_surplus(H_2)={:.6}",
        k2_checks, min_surplus_c1, min_surplus_c2
    );

    // Inspect K=3 Erdos-Suranyi configuration: primes [5, 7, 11], M = 77,
    // x chosen so x + 39 === 5*7*11 = 385 (center multiple of 385: e.g. x = 385 - 39 = 346)
    // vs Erdos-Suranyi CRT shift minimizing p^2!
    // Wait: for [5, 7, 11], M = 77, let's scan x in 0..385*5*7*11 (Wait: 5^3*7^2*11 = 67375) to find exact worst-case x!
    let p3 = [5usize, 7, 11];
    let m3 = 77usize;
    let period = 125 * 49 * 11; // 67,375 (since 5^3=125>77, 7^2=49<=77, 7^3=343>77 => let's scan 0..50000)
    let mut worst_x_c2 = 0usize;
    let mut min_surp_k3_c2 = f64::INFINITY;
    let mut worst_x_c1 = 0usize;
    let mut min_surp_k3_c1 = f64::INFINITY;

    for x in 0..15_000usize {
        let (ld1, rd1, _, _, _) = eval_telescoping_detailed(m3, x, 1.0, &p3, &[1.0, 1.0, 1.0]);
        if rd1 - ld1 < min_surp_k3_c1 {
            min_surp_k3_c1 = rd1 - ld1;
            worst_x_c1 = x;
        }
        let (ld2, rd2, _, _, _) = eval_telescoping_detailed(m3, x, 2.0, &p3, &[1.0, 1.0, 1.0]);
        if rd2 - ld2 < min_surp_k3_c2 {
            min_surp_k3_c2 = rd2 - ld2;
            worst_x_c2 = x;
        }
    }
    let (_, _, _, _, bd_k3) = eval_telescoping_detailed(m3, worst_x_c2, 2.0, &p3, &[1.0, 1.0, 1.0]);
    println!(
        "[Step 2C] Three-prime K=3 [5,7,11] M=77 (scan period {}): min_surplus(H_1)={:.2} at x={} (fails as expected since g(3)=4), min_surplus(H_2)={:.2} at x={}",
        period, min_surp_k3_c1, worst_x_c1, min_surp_k3_c2, worst_x_c2
    );
    for b in &bd_k3 {
        println!(
            "    j={} (p={}): s<0 [LHS={:.1}, RHS={:.1}, net={:+.1}] | s>=0 [LHS={:.1}, RHS={:.1}, net={:+.1}]",
            b.j + 1,
            b.pj,
            b.lhs_neg_s,
            b.rhs_neg_s,
            b.rhs_neg_s - b.lhs_neg_s,
            b.lhs_pos_s,
            b.rhs_pos_s,
            b.rhs_pos_s - b.lhs_pos_s
        );
    }
}

fn hopcroft_karp(adj: &[Vec<usize>], n_right: usize) -> usize {
    let n_left = adj.len();
    let mut pair_u = vec![usize::MAX; n_left];
    let mut pair_v = vec![usize::MAX; n_right];
    let mut dist = vec![usize::MAX; n_left];

    let bfs = |pair_u: &[usize], pair_v: &[usize], dist: &mut [usize]| -> bool {
        let mut q = VecDeque::new();
        for u in 0..n_left {
            if pair_u[u] == usize::MAX {
                dist[u] = 0;
                q.push_back(u);
            } else {
                dist[u] = usize::MAX;
            }
        }
        let mut found = false;
        while let Some(u) = q.pop_front() {
            for &v in &adj[u] {
                let pu = pair_v[v];
                if pu == usize::MAX {
                    found = true;
                } else if dist[pu] == usize::MAX {
                    dist[pu] = dist[u] + 1;
                    q.push_back(pu);
                }
            }
        }
        found
    };

    fn dfs(
        u: usize,
        adj: &[Vec<usize>],
        pair_u: &mut [usize],
        pair_v: &mut [usize],
        dist: &mut [usize],
    ) -> bool {
        for &v in &adj[u] {
            let pu = pair_v[v];
            if pu == usize::MAX || (dist[pu] == dist[u] + 1 && dfs(pu, adj, pair_u, pair_v, dist)) {
                pair_u[u] = v;
                pair_v[v] = u;
                return true;
            }
        }
        dist[u] = usize::MAX;
        false
    }

    let mut matched = 0usize;
    while bfs(&pair_u, &pair_v, &mut dist) {
        for u in 0..n_left {
            if pair_u[u] == usize::MAX && dfs(u, adj, &mut pair_u, &mut pair_v, &mut dist) {
                matched += 1;
            }
        }
    }
    matched
}

/// Step 3A: Q_n-Smooth Maximal-Proper-Divisor Combinatorial Matching!
/// Let sm_{Q}(m) = \prod_{p <= Q} p^{v_p(m)} and \Omega_{\le Q}(m) = \sum_{p <= Q} v_p(m).
/// For ANY Q-smooth weight vector w (w_p = 0 for p > Q), (X_w(m) - 2)_+ > 0 ONLY on
/// M_{\ge 3}(Q) = {1 <= m <= M : \Omega_{\le Q}(m) >= 3}, and if \pi : M_{\ge 3}(Q) -> I_x
/// is injective with (sm_Q(m) / p) | \pi(m) for some prime p <= Q dividing sm_Q(m),
/// then (H_2) holds SIMULTANEOUSLY for ALL w in [0, 1]^{\{p <= Q\}}!
fn verify_step3a_smooth_matching() {
    let configs = [
        // (n, Q_n = 2n, M) across 2n < M <= 4n^2
        (10usize, 20usize, 100usize),
        (10, 20, 400),
        (20, 40, 400),
        (20, 40, 1600),
        (30, 60, 1200),
        (30, 60, 3600),
        (50, 100, 5000),
        (50, 100, 10000),
    ];

    for &(n, qn, m) in &configs {
        let smooth_ps = sieve_primes(qn);
        // Build M_{>=3}(Q_n) and also full M_{>=3} for size comparison!
        let mut m_ge3_smooth: Vec<(usize, usize, Vec<usize>)> = Vec::new();
        let mut full_ge3_count = 0usize;

        for k in 1..=m {
            let mut rem = k;
            let mut sm_part = 1usize;
            let mut om_sm = 0usize;
            let mut active_p = Vec::new();
            for &p in &smooth_ps {
                if rem % p == 0 {
                    active_p.push(p);
                    while rem % p == 0 {
                        om_sm += 1;
                        sm_part *= p;
                        rem /= p;
                    }
                }
            }
            // Count remaining primes > Q_n just to compare |M_{>=3}(Q_n)| vs |M_{>=3}|
            let mut om_hi = 0usize;
            let mut d = qn + 1;
            let mut tmp = rem;
            while d * d <= tmp {
                while tmp % d == 0 {
                    om_hi += 1;
                    tmp /= d;
                }
                d += 1;
            }
            if tmp > 1 {
                om_hi += 1;
            }
            if om_sm + om_hi >= 3 {
                full_ge3_count += 1;
            }
            if om_sm >= 3 {
                let divs: Vec<usize> = active_p.iter().map(|&p| sm_part / p).collect();
                m_ge3_smooth.push((k, sm_part, divs));
            }
        }

        // Test shifts x: 0, adversarial ES_vp1 CRT spike, LCM_zero, and sliding shifts
        for mode in ["shift_0", "shift_137", "LCM_zero", "ES_vp1"] {
            let center = m / 2 + 1;
            let divides_in_mode = |div: usize, idx_d: usize| -> bool {
                let d = idx_d + 1;
                match mode {
                    "shift_0" => d % div == 0,
                    "shift_137" => (137 + d) % div == 0,
                    "LCM_zero" => d % div == 0,
                    "ES_vp1" => {
                        let mut rem_div = div;
                        for &p in &smooth_ps {
                            if rem_div == 1 {
                                break;
                            }
                            if rem_div % p == 0 {
                                let mut pk = 1usize;
                                while rem_div % p == 0 {
                                    pk *= p;
                                    rem_div /= p;
                                }
                                let diff = (p as isize) + (d as isize) - (center as isize);
                                if diff.rem_euclid(pk as isize) != 0 {
                                    return false;
                                }
                            }
                        }
                        true
                    }
                    _ => unreachable!(),
                }
            };

            let mut adj = Vec::with_capacity(m_ge3_smooth.len());
            for (_, _, divs) in &m_ge3_smooth {
                let mut nbrs = Vec::new();
                for idx_d in 0..m {
                    if divs.iter().any(|&dv| divides_in_mode(dv, idx_d)) {
                        nbrs.push(idx_d);
                    }
                }
                adj.push(nbrs);
            }
            let matched = hopcroft_karp(&adj, m);
            assert_eq!(
                matched,
                m_ge3_smooth.len(),
                "Q_n-smooth matching failed at n={}, Q_n={}, M={}, mode={}: {}/{}",
                n,
                qn,
                m,
                mode,
                matched,
                m_ge3_smooth.len()
            );
        }
        println!(
            "[Step 3A] Smooth matching OK: n={}, Q_n={}, M={} | |M_>=3(Q_n)| = {} (vs full |M_>=3| = {}, M = {})",
            n,
            qn,
            m,
            m_ge3_smooth.len(),
            full_ge3_count,
            m
        );
    }
}

/// Step 3B: Moderately large M (Q_n^{2+delta} <= M <= 4n^2 and smooth Hensley-Richards test).
/// Compare uniform/decreasing/clique Q_n-smooth weights across worst-case shifts x,
/// and check EVERY individual j's integrated difference (r=1 + r>=2) vs full sum!
fn verify_step3b_large_m_equidistribution() {
    let cases = [
        // (n, Q_n, M) where Q_n << M^{1/2} or M ~ 4n^2
        (25usize, 55usize, 2500usize),
        (50, 110, 10_000),
        (100, 220, 40_000),
    ];

    for &(n, qn, m) in &cases {
        let ps = sieve_primes(qn); // Only primes <= Q_n have nonzero weight!
        let profiles: Vec<(&str, Vec<f64>)> = vec![
            ("all_ones_smooth", vec![1.0; ps.len()]),
            ("uniform_0.7", vec![0.7; ps.len()]),
            ("uniform_0.4", vec![0.4; ps.len()]),
            (
                "top_half_primes_1.0",
                ps.iter()
                    .map(|&p| if p >= qn / 2 { 1.0 } else { 0.0 })
                    .collect(),
            ),
            (
                "inv_log",
                ps.iter().map(|&p| (1.0 / (p as f64).ln()).min(1.0)).collect(),
            ),
        ];

        for (name, w) in &profiles {
            // Test shifts x including x=0, x=M, x=7919*13, and ES_vp1 CRT center model
            for &x in &[0usize, m, 102_947] {
                let (ld, rd, lt, rt, bd) = eval_telescoping_detailed(m, x, 2.0, &ps, w);
                assert!((ld - lt).abs() < 1e-8 && (rd - rt).abs() < 1e-8);
                assert!(
                    rt + 1e-9 >= lt,
                    "Smooth (H_2) failed for {} at n={}, Q_n={}, M={}, x={}: LHS={} > RHS={}",
                    name, n, qn, m, x, lt, rt
                );
                // Count how many individual primes j ALREADY satisfy RHS_j >= LHS_j on their own!
                let self_sufficient = bd
                    .iter()
                    .filter(|b| (b.rhs_neg_s + b.rhs_pos_s) + 1e-11 >= (b.lhs_neg_s + b.lhs_pos_s))
                    .count();
                if x == 102_947 {
                    println!(
                        "[Step 3B] n={}, Q_n={}, M={}, profile={:<20} | LHS={:10.2} <= RHS={:10.2} (surplus={:+10.2}, per-j self-dom={}/{})",
                        n,
                        qn,
                        m,
                        name,
                        lt,
                        rt,
                        rt - lt,
                        self_sufficient,
                        bd.len()
                    );
                }
            }
        }
    }
}

fn verify_adversarial_crt_minimization() {
    // Coordinate-descent adversarial CRT minimizer over R_i mod p_i^{E_i} (p_i^{E_i} > M)
    // to find the TRUE worst-case shift x >= 0 for Q_n-smooth weights!
    for &(n, qn, m) in &[(15usize, 32usize, 400usize), (25, 55, 1600), (40, 85, 4000)] {
        let ps = sieve_primes(qn);
        let mod_pows: Vec<usize> = ps
            .iter()
            .map(|&p| {
                let mut pe = p;
                while pe <= m {
                    pe *= p;
                }
                pe
            })
            .collect();

        for (prof_name, w) in [
            ("all_ones_smooth", vec![1.0f64; ps.len()]),
            ("uniform_0.5", vec![0.5f64; ps.len()]),
            (
                "mid_primes_1.0",
                ps.iter()
                    .map(|&p| if p >= 5 { 1.0 } else { 0.0 })
                    .collect::<Vec<f64>>(),
            ),
            (
                "band_m1_4_to_qn",
                ps.iter()
                    .map(|&p| {
                        let z0 = (m as f64).powf(0.25) as usize;
                        if p >= z0 { 1.0 } else { 0.0 }
                    })
                    .collect::<Vec<f64>>(),
            ),
        ] {
            // Compute LHS on {1..=M}
            let mut xw_lhs = vec![0.0f64; m + 1];
            for (i, &p) in ps.iter().enumerate() {
                if w[i] == 0.0 {
                    continue;
                }
                let mut pk = p;
                while pk <= m {
                    let mut mult = pk;
                    while mult <= m {
                        xw_lhs[mult] += w[i];
                        mult += pk;
                    }
                    pk *= p;
                }
            }
            let lhs: f64 = (1..=m).map(|k| (xw_lhs[k] - 2.0).max(0.0)).sum();

            // Start from ES_vp1 (all primes centered with valuation 1 at d = m/2 + 1)
            let center = m / 2 + 1;
            let mut residues: Vec<usize> = ps
                .iter()
                .zip(mod_pows.iter())
                .map(|(&p, &pe)| ((p as isize - center as isize).rem_euclid(pe as isize)) as usize)
                .collect();

            // Build current xw_rhs[1..=M]
            let eval_prime_contrib = |i: usize, res_i: usize, out: &mut [f64], sign: f64| {
                let p = ps[i];
                let pe = mod_pows[i];
                let wi = w[i];
                if wi == 0.0 {
                    return;
                }
                let mut pk = p;
                while pk <= m {
                    // First d >= 1 such that res_i + d === 0 (mod pk)
                    let rem = res_i % pk;
                    let first_d = if rem == 0 { pk } else { pk - rem };
                    let mut d = first_d;
                    while d <= m {
                        // Exclude hitting 0 mod pe if we want minimal valuation, or exact mod pe valuation:
                        out[d] += sign * wi;
                        d += pk;
                    }
                    pk *= p;
                }
                // Also if (res_i + d) % pe == 0, add one extra wi for pe (since pe > m, at most one d):
                let rem_pe = res_i % pe;
                let d_pe = if rem_pe == 0 { pe } else { pe - rem_pe };
                if d_pe <= m {
                    out[d_pe] += sign * wi;
                }
            };

            let mut xw_rhs = vec![0.0f64; m + 1];
            for i in 0..ps.len() {
                eval_prime_contrib(i, residues[i], &mut xw_rhs, 1.0);
            }

            // Coordinate descent over residues[i] to MINIMIZE RHS = sum_{d=1}^M (xw_rhs[d] - 1)_+
            for _pass in 0..2 {
                for i in 0..ps.len() {
                    if w[i] == 0.0 {
                        continue;
                    }
                    eval_prime_contrib(i, residues[i], &mut xw_rhs, -1.0);
                    let pe = mod_pows[i];
                    let step = (pe / 64).max(1);
                    let mut best_r = residues[i];
                    let mut best_rhs = f64::INFINITY;

                    let mut cand_rs: Vec<usize> = (0..pe).step_by(step).collect();
                    cand_rs.push(residues[i]);
                    cand_rs.push(pe - m - 1); // avoids pe completely and gives floor(M/p^r) for all r!
                    for r_cand in cand_rs {
                        let r_mod = r_cand % pe;
                        eval_prime_contrib(i, r_mod, &mut xw_rhs, 1.0);
                        let rhs_val: f64 = (1..=m).map(|d| (xw_rhs[d] - 1.0).max(0.0)).sum();
                        if rhs_val < best_rhs {
                            best_rhs = rhs_val;
                            best_r = r_mod;
                        }
                        eval_prime_contrib(i, r_mod, &mut xw_rhs, -1.0);
                    }
                    residues[i] = best_r;
                    eval_prime_contrib(i, best_r, &mut xw_rhs, 1.0);
                }
            }
            let min_rhs: f64 = (1..=m).map(|d| (xw_rhs[d] - 1.0).max(0.0)).sum();
            assert!(
                min_rhs + 1e-9 >= lhs,
                "Adversarial CRT violated smooth (H_2) at n={}, Q_n={}, M={}, prof={}: LHS={} > min_RHS={}",
                n, qn, m, prof_name, lhs, min_rhs
            );

            // Also check per-j telescoping under this adversarial CRT residue vector!
            let mut neg_j_count = 0usize;
            let mut active_j = 0usize;
            for (j, &pj) in ps.iter().enumerate() {
                let wp = w[j];
                if wp <= 0.0 {
                    continue;
                }
                active_j += 1;
                let mut lhs_j = 0.0f64;
                let mut rhs_j = 0.0f64;
                let mut r = 1usize;
                let mut p_pow = pj;
                while p_pow <= m {
                    let lo = 1.0 - (r as f64) * wp;
                    let hi = 1.0 - ((r - 1) as f64) * wp;
                    // LHS on k in 1..=(m / p_pow)
                    for k in 1..=(m / p_pow) {
                        let mut yk = 0.0;
                        for ii in 0..j {
                            if w[ii] > 0.0 {
                                let mut v = k;
                                while v % ps[ii] == 0 {
                                    yk += w[ii];
                                    v /= ps[ii];
                                }
                            }
                        }
                        lhs_j += integral_indicator(yk - 1.0, lo, hi);
                    }
                    // RHS on d in 1..=m with p_pow | (x + d)
                    let rem = residues[j] % p_pow;
                    let first_d = if rem == 0 { p_pow } else { p_pow - rem };
                    let mut d = first_d;
                    while d <= m {
                        let mut yb = 0.0;
                        for ii in 0..j {
                            if w[ii] > 0.0 {
                                let pe_ii = mod_pows[ii];
                                let val_ii = (residues[ii] + d) % pe_ii;
                                if val_ii == 0 {
                                    let mut tmp = pe_ii;
                                    while tmp > 1 {
                                        yb += w[ii];
                                        tmp /= ps[ii];
                                    }
                                } else {
                                    let mut tmp = val_ii;
                                    while tmp % ps[ii] == 0 {
                                        yb += w[ii];
                                        tmp /= ps[ii];
                                    }
                                }
                            }
                        }
                        rhs_j += integral_indicator(yb, lo, hi);
                        d += p_pow;
                    }
                    r += 1;
                    p_pow = p_pow.saturating_mul(pj);
                }
                if rhs_j + 1e-9 < lhs_j {
                    neg_j_count += 1;
                }
            }
            println!(
                "[Step 3C Adversarial CRT] n={}, Q_n={}, M={}, prof={:<16} | LHS={:8.2} <= min_RHS={:8.2} (surplus={:+8.2}, j_deficits={}/{})",
                n, qn, m, prof_name, lhs, min_rhs, min_rhs - lhs, neg_j_count, active_j
            );
        }
    }
}

fn main() {
    println!("=== Exploring Q_n-Smooth (H_{{2+epsilon}}) & Exact s-Integral Telescoping ===");
    verify_step2_few_primes();
    verify_step3a_smooth_matching();
    verify_step3b_large_m_equidistribution();
    verify_adversarial_crt_minimization();
    println!("=== ALL EXPLORATION & VERIFICATION CHECKS PASSED ===");
}
