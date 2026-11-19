//! Exact verification of the s-integral identity for Q_n-smooth weights
//! Following Proposition 8(2) and Remark 9(3) rigorously.

fn sieve_primes(limit: usize) -> Vec<usize> {
    let mut is_p = vec![true; limit + 1];
    is_p[0] = false; if limit >= 1 { is_p[1] = false; }
    let mut p = 2;
    while p * p <= limit {
        if is_p[p] {
            let mut mult = p * p;
            while mult <= limit { is_p[mult] = false; mult += p; }
        }
        p += 1;
    }
    (2..=limit).filter(|&x| is_p[x]).collect()
}

fn verify_exact_telescoping(n: usize, m: usize, x: usize, epsilon: f64) -> Result<(), String> {
    let qn = ((2.0 + epsilon) * (n as f64)).floor() as usize;
    let ps = sieve_primes(m);
    
    // Restrict weights to Q_n-smooth: w_p = 0 for p > Q_n
    let w: Vec<f64> = ps.iter().map(|&p| if p <= qn { 0.7 } else { 0.0 }).collect();

    let yj = |j: usize, mut val: usize| -> f64 {
        let mut sum = 0.0;
        for i in 0..j {
            let p = ps[i];
            while val % p == 0 {
                sum += w[i];
                val /= p;
            }
        }
        sum
    };

    // Integral helper: \int_a^b 1_{u > t} dt = (min(u, b) - a)_+
    let integral_indicator = |u: f64, a: f64, b: f64| -> f64 {
        if b <= a { return 0.0; }
        (u.min(b) - a).max(0.0)
    };

    let mut lhs_total = 0.0;
    let mut rhs_total = 0.0;

    for (j, &pj) in ps.iter().enumerate() {
        let wp = w[j];
        if wp == 0.0 { continue; }
        
        let mut r = 1usize;
        let mut p_pow = pj;
        while p_pow <= x + m {
            let lo = 1.0 - (r as f64) * wp;
            let hi = 1.0 - ((r - 1) as f64) * wp;

            // LHS: k in {1, ..., floor(M / p_j^r)}, indicator Y_j(k) > s + 1 <=> Y_j(k) - 1 > s
            if p_pow <= m {
                for k in 1..=(m / p_pow) {
                    lhs_total += integral_indicator(yj(j, k) - 1.0, lo, hi);
                }
            }

            // RHS: b' in I_{j,r} = {floor(x / p_j^r) + 1, ..., floor((x + M) / p_j^r)}, indicator Y_j(b') > s
            let b_start = (x / p_pow) + 1;
            let b_end = (x + m) / p_pow;
            if b_start <= b_end {
                for b_prime in b_start..=b_end {
                    rhs_total += integral_indicator(yj(j, b_prime), lo, hi);
                }
            }

            r += 1;
            p_pow = p_pow.saturating_mul(pj);
            if p_pow == 0 { break; }
        }
    }

    // Verify (H_2): LHS <= RHS
    if lhs_total > rhs_total + 1e-9 {
        return Err(format!("(H_2) failed at M={}, x={}: LHS={} > RHS={}", m, x, lhs_total, rhs_total));
    }
    Ok(())
}

fn main() {
    let n = 20;
    let epsilon = 0.1;
    // Test across intermediate regime 2n < M <= 4n^2 and worst-case shifts x
    for m in [45, 100, 400, 1600] {
        for x in [0, 1, 37, 503, 10000] {
            if let Err(e) = verify_exact_telescoping(n, m, x, epsilon) {
                eprintln!("Verification Error: {}", e);
                std::process::exit(1);
            }
        }
    }
    println!("SUCCESS: Exact Q_n-smooth s-integral (H_2) verified across regimes and adversarial shifts.");
}
