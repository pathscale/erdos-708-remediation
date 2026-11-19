# Erdős Problem #708 — Paper III: Scaled-Interval Hinge Telescoping, Difference-of-Convex Obstructions, and Smooth Proper-Divisor Matching

Standalone manuscript, DualKernel-verified Lean 4 formalization (`51` declarations, `0` `sorry`s), and zero-dependency Rust verification suite for Paper III of the Erdős Problem #708 program.

- **Zenodo Archive (This Paper, Lean 4 Formalization & Suite):** `10.5281/zenodo.24366998` (`https://doi.org/10.5281/zenodo.24366998`)
- **Paper I (Exact Small-$n$ Values & Certificate):** `10.5281/zenodo.24366897` (`https://doi.org/10.5281/zenodo.24366897`)
- **Paper II (Whole-Cofactor Peeling & $8.83n$ Asymptotic Bound):** `10.5281/zenodo.24342717` (`https://doi.org/10.5281/zenodo.24342717`)

## Contents

- `paper/erdos708-smooth-hinge.pdf` (`paper/erdos708-smooth-hinge.typ`, `paper/erdos708-smooth-hinge.tex`, `paper/references.bib`): Paper III manuscript proving the scaled-interval $s$-integral equivalence and negative-$s$ dominance (Proposition 1), unconditional pointwise dominance for $K \le 2$ primes at all $c \ge 1$ (Theorem 2), the five-prime difference-of-convex counterexample refuting binary vertex reduction (Proposition 3), discrete intermediate-value divisor peeling for high prime powers (Theorem 4), and $Q_n$-smooth proper-divisor matching + binary smooth sieve bounds (Theorem 5), alongside the three open analytical obligations separating Paper II from $g(n) \le (2 + o(1))n$.
- `lean_formalization/`: Five Lean 4 modules (`Prop8.lean`, `HingeInequality.lean`, `Theorem3.lean`, `Corollary4.lean`, `Theorem6.lean`) verified with `0` `sorry`s (`51` declarations).
- `verify_s_integral_corrected.rs`, `explore_h2_smooth.rs`, `verify_three_final_checks.rs`: Zero-dependency Rust 2021 verification programs.
- `NUMBERS.md`: Provenance and SHA-256 hashes of every numerical constant in the manuscript.
- `notes.md`: Plain-English overview of Papers I–III.

## Verification Commands

Compile and run all three standalone Rust verifiers:

```sh
rustc -O --edition 2021 verify_s_integral_corrected.rs -o /tmp/verify_s_integral_corrected && /tmp/verify_s_integral_corrected
rustc -O --edition 2021 explore_h2_smooth.rs -o /tmp/explore_h2_smooth && /tmp/explore_h2_smooth
rustc -O --edition 2021 verify_three_final_checks.rs -o /tmp/verify_three_final_checks && /tmp/verify_three_final_checks
```

Compile the manuscript PDF:

```sh
typst compile paper/erdos708-smooth-hinge.typ paper/erdos708-smooth-hinge.pdf
```

Verify all SHA-256 checksums:

```sh
shasum -a 256 -c SHA256SUMS.txt
```
