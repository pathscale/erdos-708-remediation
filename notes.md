# Erdős Problem #708 — Plain-English Journal Notes

## Plain-English Breakdown

- **The Core Problem (Erdős #708):** Suppose you pick a set $A$ of $n$ integers ($\ge 2$), where the largest number in your set is $M$. Now look at *any* shifted block of $M$ consecutive positive integers, $I_x = \{x + 1, \dots, x + M\}$. In the worst case (across all choices of $A$ and all starting shifts $x \ge 0$), how many numbers $g(n)$ must you pick from $I_x$ so that their product is divisible by the product of everything in $A$? Erdős and Surányi proved in 1959 that you sometimes need $(2 - o(1))n$ picks, and Erdős conjectured that for large $n$ you never need more than $(2 + o(1))n$ — roughly $2n$ picks.

- **Paper I (Exact Small Cases):** Extending Erdős and Surányi's classic $g(3) = 4$, Paper I maps out how prime powers collide at a central element using the Chinese Remainder Theorem (CRT), strips out that collision via a GCD–LCM tree, and runs pruned branch-and-bound searches on the remaining punctured interval. This pins down the exact values $g(4) = 5$, $g(5) = 6$, and $g(6) = 8$, and constructs asymmetric prime-pair families proving $g(7) \ge 9$ and $g(8) \ge 11$.

- **Paper II (A Better Global Upper Bound — $\approx 8.83n$):** Previous linear-programming (LP) approaches paid an extra $+2n$ rounding penalty from large primes. Instead of rounding everything at once, Paper II *peels* away every number carrying a large prime factor ($\ge Q$) **together with its entire smooth cofactor** in fewer than $2$ picks per element whenever $Q^2 > M$. Only "smooth" numbers (built strictly from primes $< Q_n$) remain, where the number of active primes is $\pi(Q_n - 1) = o(n)$ rather than $\Theta(n)$. Eliminating that $+2n$ surcharge gives $\le 3n$ picks whenever $M \ge 9n^2$ and drops the unconditional global bound by ~20%, from $11n$ down to $(56501 / 6400 + o(1))n \approx 8.83n$ (with $g(n) \le 10n$ for all $n \ge 1{,}446$).

- **Paper III (Path to the Full $(2 + o(1))n$ Conjecture):** Paper III attacks the remaining gap on $Q_n$-smooth numbers using two complementary tools:
  1. **Prime-by-prime $s$-integral telescoping:** Rewrites the dual hinge inequality $(H_{2+\varepsilon})$ as an integral over scaled intervals $I_{j,r} = \{\lfloor x/p_j^r \rfloor + 1, \dots, \lfloor (x+M)/p_j^r \rfloor\}$, proving unconditional dominance for all negative thresholds $s < 0$, all one- and two-prime weight vectors $w \in [0, 1]^2$, and high prime powers $p_j^r > M/L_0$ (via divisor peeling).
  2. **Smooth proper-divisor matching:** Shows that matching each number $m \le M$ having $\ge 3$ smooth prime factors into $I_x$ via a single smooth proper divisor ($\operatorname{sm}_{Q_n}(m)/p \mid \pi(m)$) implies $(H_2)$ across *all* continuous dual weights $w \in [0, 1]^{\{p \le Q_n\}}$ at once — side-stepping a proven non-convexity trap where interior weights like $w_p = 1/2$ beat every $0$-$1$ corner.

---

## Quick Status Reference for the Journal Entry

### Proved Unconditionally (Manuscript + 51 DualKernel Lean 4 Declarations)
- Exact finite values: $g(1)=1, \, g(2)=2, \, g(3)=4, \, g(4)=5, \, g(5)=6, \, g(6)=8$, and $g(7) \ge 9, \, g(8) \ge 11$.
- Global asymptotic bound: $g(n) \le (56501/6400 + o(1))n < (8.8283 + o(1))n$, with $g(n) \le 10n$ for $n \ge 1{,}446$, and $\tau(A, I_x) \le 3n$ for all $M \ge 9n^2$.
- Universal semiprime multigraph saving bound: $\tau(G, I_x) \le 2|E| - \lceil |V_{\text{non-iso}}|/2 \rceil$ (and $2|E| - \max(|P_{\text{non-iso}}|, |Q_{\text{non-iso}}|)$ when bipartite).
- Smooth $s$-integral reductions: negative-$s$ dominance for all shifts $x \ge 0$, complete $K \le 2$ pointwise $(H_c)$ ($c \ge 1$), explicit $4$-prime difference-of-convex counterexample refuting naive $0$-$1$ extreme-point reduction, $L_0$-truncated $r \ge 3$ divisor-peeling reduction, and $100\%$ computational verification of smooth matching up to $M = 15{,}120$.

### Remaining Open Steps Before Claiming Unconditional $g(n) \le (2 + o(1))n$
1. **Analytical Hall's Marriage proof for smooth matching** ($\mathcal{M}_{\ge 3}(Q_n) \hookrightarrow I_x$) across *all* exponentially large CRT shifts $x \ge 0$ on $(2 + \varepsilon)n \le M < Q_n^2$ (note that on $(2+\varepsilon)n \le M \le 4Q_n \approx 8n$, every $m \le M$ with $\Omega(m) \ge 3$ already has $p_{\max}(m) \le Q_n$, so smooth matching coincides with unsmoothed Proposition 8(1)), *or* a continuous multi-scale $s$-integral bound on medium primes $p \in (L_{j,1}^\eta, Q_n]$.
2. **Coupled sub-cubic bridge ($n^2 \ln^2 n \lesssim M < 8n^3$):** Above $M \asymp n^2 \ln^2 n$, $\pi(M^{1/2})$ exceeds $n$, so closing $(2 + o(1))n$ up to Chen's $8n^3$ threshold requires coupling medium primes rather than uncoupled $\lfloor M^{1/2} \rfloor$-smooth LP vertex rounding.
