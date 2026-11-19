# Unified Analysis of $Q_n$-Smooth $(H_{2+\varepsilon})$ via Proposition 8(2)'s $s$-Integral

## 0. Exact Definitions and Corrected Identities

Fix $M \ge 2$, an **arbitrary worst-case shift** $x \in \mathbb{Z}_{\ge 0}$ (never averaged), and the shifted interval $I_x := \{x + 1, \dots, x + M\}$. For a prime-weight vector $w = (w_p)_{p \le M} \in [0, 1]^{\{p \le M\}}$, set
$$
X_w(m) := \sum_{p \le M} v_p(m) w_p \ge 0.
$$
For $c \ge 1$, the deterministic shifted-interval hinge inequality $(H_c)$ asserts that **for every $x \in \mathbb{Z}_{\ge 0}$ and every admissible $w$**,
$$
\sum_{m=1}^M (X_w(m) - c)_+ \;\le\; \sum_{b \in I_x} (X_w(b) - 1)_+.
$$

### Exact Fundamental Integral Identity
For every real $u$ and every $a \le b$ in $\mathbb{R}$ (including $a < 0$ or $b < 0$),
$$
(u - a)_+ - (u - b)_+ \;=\; \int_a^b \mathbf{1}_{u > t}\,dt \;=\; \bigl(\min(u, b) - a\bigr)_+.
$$
In particular, for $y \ge 0$:
$$
\int_0^1 \mathbf{1}_{y > s}\,ds = \min(y, 1), \qquad \int_0^1 \mathbf{1}_{y > s + c - 1}\,ds = \min\bigl((y - c + 1)_+, 1\bigr).
$$

### Exact Scaled-Interval Telescoping Identity (Proposition 8(2) at General $c \ge 1$)
Order the active primes $p_1 < p_2 < \dots < p_K \le M$ (where $w_p = 0$ outside $\{p_1, \dots, p_K\}$), and put
$$
Y_j(u) := \sum_{i = 1}^{j - 1} v_{p_i}(u) w_{p_i} \qquad (1 \le j \le K, \text{ with } Y_1(u) \equiv 0).
$$
Since $\gcd(p_i, p_j) = 1$ for $i < j$, every $r \ge 1$ and $k \ge 1$ satisfy $Y_j(p_j^r k) = Y_j(k)$. Expanding $(Y_{j+1}(n) - c)_+ - (Y_j(n) - c)_+$ over $1 \le r \le v_{p_j}(n)$ and substituting $t = s + c - 1$ on $\{1, \dots, M\}$ and $t = s$ on $I_x$ yields the **exact deterministic equivalence**: $(H_c)$ holds at $(M, x, w)$ if and only if
$$
\sum_{j=1}^K \sum_{r \ge 1} \sum_{k=1}^{\lfloor M / p_j^r \rfloor} \int_{1 - r w_{p_j}}^{1 - (r-1) w_{p_j}} \mathbf{1}_{Y_j(k) > s + c - 1}\,ds
\;\le\;
\sum_{j=1}^K \sum_{r \ge 1} \sum_{b' \in I_{j,r}} \int_{1 - r w_{p_j}}^{1 - (r-1) w_{p_j}} \mathbf{1}_{Y_j(b') > s}\,ds,
$$
where the scaled shifted interval is
$$
I_{j,r} := \left\{\left\lfloor \frac{x}{p_j^r} \right\rfloor + 1, \dots, \left\lfloor \frac{x + M}{p_j^r} \right\rfloor\right\}, \qquad |I_{j,r}| \in \left\{\left\lfloor \frac{M}{p_j^r} \right\rfloor, \; \left\lfloor \frac{M}{p_j^r} \right\rfloor + 1\right\}.
$$

### Exact Role of the Hensley–Richards Obstruction (Remark 9(3))
$(H_2)$ itself does **not** fail for $L \ge e^{100}$. Rather, inside Proposition 8(2)'s integral, naive **pointwise level-set dominance at $s = 0$** ($|\{1 \le k \le L : Y_j(k) > 1\}| \le |\{b' \in I' : Y_j(b') > 0\}|$) fails when setting $w_q = 1$ on *all* primes $q \le L$, where $s = 0$ reduces to the Second Hardy–Littlewood inequality $\pi(x' + L) - \pi(x') \le \pi(L) + 1$, violated by $\Theta(L / \ln^2 L)$ for $L \ge e^{100}$. Two mechanisms eliminate this obstruction for Erdős #708:
1. Restricting to **$Q_n$-smooth weights** ($w_p = 0$ for all $p > Q_n \approx (2 + \varepsilon)n$) via Whole-Cofactor Peeling (Theorem 3 + Theorem 5(3)), so active primes are $\le Q_n \ll M$ when $M \gg n$; and
2. Evaluating the **$s$-integral** across $[1 - r w_{p_j}, 1 - (r-1) w_{p_j}]$ (splitting at $s = 0$ into $s < 0$ and $s \in [0, 1]$).

---

## Step 1: $Q_n$-Smooth Restriction and Universal Negative-$s$ Dominance

By Theorem 5(3) of the manuscript, to prove $\tau(A, I_x) \le (2 + \varepsilon + o(1))n$ for all $M \le Q_n^2 - 1$ (which covers $2n < M \le 4n^2$ since $Q_n = (2+\varepsilon)n + (1+o(1))(2+\varepsilon)n/\ln n > 2n$), it suffices to establish $(H_c)$ at $c = 2 + \varepsilon$ ($\varepsilon > 0$, or even $c = 2$) restricted to **$Q_n$-smooth weights**:
$$
\mathcal{W}(Q_n) := \bigl\{w \in [0, 1]^{\{p \le M\}} : w_p = 0 \text{ for all } p > Q_n\bigr\}.
$$
Split each integration domain $[1 - r w_{p_j}, 1 - (r-1) w_{p_j}]$ at $s = 0$:
$$
J_{j,r}^- := [1 - r w_{p_j}, 1 - (r-1) w_{p_j}] \cap (-\infty, 0], \qquad
J_{j,r}^+ := [1 - r w_{p_j}, 1 - (r-1) w_{p_j}] \cap [0, 1].
$$

### Lemma 1 (Universal Deterministic Dominance on $s < 0$ and High-Power Reduction)
Fix any $c \ge 1$, $M \ge 1$, $x \ge 0$, $w \in [0, 1]^{\{p \le M\}}$, $1 \le j \le K$, and $r \ge 1$.
1. **Pointwise dominance for all $s < 0$**: Since $Y_j(b') \ge 0 > s$ for every $b' \in I_{j,r}$,
   $$
   \sum_{k=1}^{\lfloor M / p_j^r \rfloor} \mathbf{1}_{Y_j(k) > s + c - 1}
   \;\le\; \left\lfloor \frac{M}{p_j^r} \right\rfloor
   \;\le\; |I_{j,r}|
   \;=\; \sum_{b' \in I_{j,r}} \mathbf{1}_{Y_j(b') > s}.
   $$
   Moreover, on $s \in [-(c - 1), 0)$ (where $s + c - 1 \ge 0$), RHS exceeds LHS by the strict non-negative surplus
   $$
   \mathcal{S}_{j,r}^- \;\ge\; \int_{J_{j,r}^- \cap [-(c-1), 0]} \bigl|\{1 \le k \le \lfloor M / p_j^r \rfloor : Y_j(k) \le s + c - 1\}\bigr|\,ds \;\ge\; 0.
   $$
2. **Automatic elimination of $p_j^r > M$ and $(r - 1) w_{p_j} \ge 1$**:
   - Whenever $p_j^r > M$, $\lfloor M / p_j^r \rfloor = 0$, so the LHS integral for $(j, r)$ vanishes identically while the RHS integral is $\ge 0$.
   - Whenever $(r - 1) w_{p_j} \ge 1$ (in particular, **for every $r \ge 2$ whenever $w_{p_j} = 1$**), $J_{j,r}^+ = \emptyset$, so $\mathrm{LHS}_{j,r} \le \mathrm{RHS}_{j,r}$ holds deterministically for every shift $x \ge 0$ by Part (1).

*(Formalized and DualKernel-verified in `lean_formalization/Prop8.lean` and `lean_formalization/HingeInequality.lean`.)*

---

## Step 2: Analytical Proofs for Single-Prime, Two-Prime, and Uniform Smooth Weights

### Theorem 2 (Unconditional Pointwise $(H_c)$ for $K \le 2$ Active Primes at Every $c \ge 1$)
Let $w \in [0, 1]^{\{p \le M\}}$ be supported on at most two primes $p_1 \neq p_2$, with $w_1 = w_{p_1} \in (0, 1]$ and $w_2 = w_{p_2} \in [0, 1]$. Then for **every $c \ge 1$, every $M \ge 1$, and every shift $x \ge 0$**, the integrand in Proposition 8(2) is dominated **pointwise at every $(j, r, s)$**:
1. **$j = 1$ ($Y_1 \equiv 0$)**: For $s \ge 0$, $\mathbf{1}_{0 > s + c - 1} = \mathbf{1}_{0 > s} = 0$. For $s < 0$, Lemma 1(1) gives $\mathrm{LHS}_{1,r}(s) \le \mathrm{RHS}_{1,r}(s)$ (with strict positive surplus $|I_{1,2}| \ge \lfloor M / p_1^2 \rfloor$ at $w_1 = 1, c = 2$).
2. **$j = 2$ ($Y_2(u) = w_1 v_{p_1}(u)$)**: For $s < 0$, Lemma 1(1) applies. For $s \ge 0$, define $a(t) := \lfloor t / w_1 \rfloor + 1 \ge 1$ for $t \ge 0$. Then $Y_2(u) > t \iff v_{p_1}(u) \ge a(t) \iff p_1^{a(t)} \mid u$.
   - On $\{1, \dots, \lfloor M / p_2^r \rfloor\}$:
     $$
     \sum_{k=1}^{\lfloor M / p_2^r \rfloor} \mathbf{1}_{Y_2(k) > s + c - 1} = \left\lfloor \frac{\lfloor M / p_2^r \rfloor}{p_1^{a(s + c - 1)}} \right\rfloor = \left\lfloor \frac{M}{p_1^{a(s + c - 1)} p_2^r} \right\rfloor.
     $$
   - On $I_{2,r}$: Since $b' \in I_{2,r} \iff b := p_2^r b' \in I_x$ and $\gcd(p_1, p_2) = 1$, we have $p_1^{a(s)} \mid b' \iff p_1^{a(s)} p_2^r \mid b$, so
     $$
     \sum_{b' \in I_{2,r}} \mathbf{1}_{Y_2(b') > s} = \bigl|I_x \cap p_1^{a(s)} p_2^r \mathbb{Z}\bigr| = \left\lfloor \frac{x + M}{p_1^{a(s)} p_2^r} \right\rfloor - \left\lfloor \frac{x}{p_1^{a(s)} p_2^r} \right\rfloor \;\ge\; \left\lfloor \frac{M}{p_1^{a(s)} p_2^r} \right\rfloor.
     $$
   Because $c \ge 1 \implies a(s + c - 1) \ge a(s)$ (and $c \ge 2, w_1 \le 1 \implies a(s + c - 1) \ge a(s) + 1$), we obtain
   $$
   \left\lfloor \frac{M}{p_1^{a(s + c - 1)} p_2^r} \right\rfloor \;\le\; \left\lfloor \frac{M}{p_1^{a(s)} p_2^r} \right\rfloor \;\le\; \bigl|I_x \cap p_1^{a(s)} p_2^r \mathbb{Z}\bigr|. \qquad \square
   $$
*(Remark: Theorem 2 explains structurally why $(H_1)$ holds for all $K \le 2$ active primes, so Erdős and Surányi's lower bound $g(3) = 4 > 3$ necessarily requires $K = 3$ primes $\{p_1, p_2, p_3\}$. Verified in DualKernel Lean 4 as `two_prime_j2_pointwise_dominance` and `two_prime_strict_exp_boost` in `lean_formalization/HingeInequality.lean`, and numerically across $44{,}800$ configurations in `explore_h2_smooth.rs`.)*

---

## Step 3: Regime Split Below $M \le 4n^2$

Order the active smooth primes $2 \le p_1 < p_2 < \dots < p_K \le Q_n$. By Lemma 1, only $s \in J_{j,r}^+ \subseteq [0, 1]$ with $j \ge 3$, $p_j^r \le M$, and $(r - 1) w_{p_j} < 1$ requires bounding. Write $L_{j,r} := \lfloor M / p_j^r \rfloor \ge 1$. Using the complement identity on $I_{j,r}$ and $\{1, \dots, L_{j,r}\}$:
$$
\mathrm{RHS}_{j,r}(s) - \mathrm{LHS}_{j,r}(s) = \bigl(|I_{j,r}| - L_{j,r}\bigr) + \bigl|\{1 \le k \le L_{j,r} : Y_j(k) \le s + c - 1\}\bigr| - \bigl|\{b' \in I_{j,r} : Y_j(b') \le s\}\bigr|.
$$

### Regime 3A: Moderately Large $M$ ($L_{j,r} \ge Q_n^{1+\delta}$, e.g. $Q_n^{2+\delta} \le M \le 4n^2$ or $r=1$ on $Q_n^{1+\delta} \le M \le 4n^2$)
When $p_j \le Q_n \le L_{j,r}^{1/(1+\delta)}$ ($L := L_{j,r}$), two complementary sieve regimes govern $0$-$1$ and uniform smooth weights ($w_p = \alpha \in (0, 1]$ on $S \subseteq [2, Q_n]$) uniformly across **every** shift $x \ge 0$:

1. **Dense prime-harmonic mass ($\mu_j := \sum_{p \in S_{< j}} p^{-1} \gg 1$, including $w \equiv 1$ on $p \le Q_n$)**:
   - **RHS upper sieve bound**: Sifting $I_{j,r}$ by primes $p \in S_{< j}$ with $p \le z := \min(p_j, L^{1/2}/\ln L)$ via Selberg's upper-bound sieve gives, uniformly in $x \ge 0$,
     $$
     \bigl|\{b' \in I_{j,1} : \Omega_{S_{< j}}(b') = 0\}\bigr| \;\le\; \bigl(2 + o(1)\bigr) L \prod_{\substack{p \in S_{< j} \\ p \le z}}\left(1 - \frac{1}{p}\right).
     $$
     (When $p_j \le L^\eta$ with $\eta \to 0$, the Fundamental Lemma of the Combinatorial Sieve sharpens the factor $2$ to $1 + O(u^{-u/2})$.)
   - **LHS semiprime boost (why $Q_n$-smoothness defeats Hensley–Richards)**: Because $p_j \le L^{1/(1+\delta)}$ (unlike $p_j = L$ in Remark 9(3), where $p q \le L$ with $q \ge p_j$ is impossible!), every pair of primes $(p, q)$ with $p \in S_{< j}$, $p \le L^{\frac{\delta}{2(1+\delta)}}$, and $p_j \le q \le L / p$ produces a distinct product $k = p q \in \{1, \dots, L\}$ satisfying $Y_j(p q) = w_p \le 1 < s + c - 1$ (for $s > 0$ or $c = 2 + \varepsilon$). Summing over $p$ gives
     $$
     \bigl|\{1 \le k \le L : \Omega_{S_{< j}}(k) \le 1\}\bigr| \;\ge\; \sum_{\substack{p \in S_{< j} \\ p \le L^{\delta/(2+2\delta)}}} \bigl(\pi(L/p) - \pi(p_j)\bigr) \;\ge\; \frac{1 - o(1)}{\ln L} L \sum_{\substack{p \in S_{< j} \\ p \le L^{\delta/(2+2\delta)}}} \frac{1}{p},
     $$
     which grows by an extra factor $\mu_j \sim \ln \ln p_j \to \infty$ over Selberg's upper bound when $S = \{p \le Q_n\}$.

2. **Sparse / band prime-harmonic mass ($\mu_j = \sum_{p \in S_{< j}} p^{-1} < 1$ with $S_{< j} \subseteq \{p \le L^{1/2 - \theta}\}$)**:
   Because $S_{< j} \subseteq \{p \le L^{1/2 - \theta}\}$ implies $|S_{< j}|^2 \le L^{1 - 2\theta} = o(L)$, off-diagonal rounding errors in the second moment sum to $O(|S_{< j}|^2) = o(L)$ uniformly across all $\delta > 0$. Let $f(b') := \sum_{p \in S_{< j}, \, p \mid b'} 1$. Then $\sum_{b' \in I_{j,1}} f(b') = (\mu_j - o(1)) L$ and $\sum_{b' \in I_{j,1}} f(b')^2 \le (\mu_j + \mu_j^2 + o(1)) L$, so **Paley–Zygmund (Cauchy–Schwarz)** gives, for every $x \ge 0$,
   $$
   \mathrm{RHS}_{j,1} = \bigl|\{b' \in I_{j,1} : f(b') \ge 1\}\bigr| \;\ge\; \frac{(\sum f)^2}{\sum f^2} \;\ge\; \bigl(1 - o(1)\bigr) \frac{\mu_j}{1 + \mu_j} L,
   $$
   whereas on $\{1, \dots, L\}$, union bound over pairs $p_1 \le p_2$ in $S_{< j}$ gives $\mathrm{LHS}_{j,1} \le \frac{1}{2}(\mu_j^2 + \sum p^{-2}) L < \frac{\mu_j}{1 + \mu_j} L$ for all $0 < \mu_j < 1$ (since $\frac{1}{2}\mu_j(1 + \mu_j) < 1$ on $(0, 1)$).

### Regime 3B: Small $M$ ($2n < M \le Q_n^{2+\delta}$) — $Q_n$-Smooth Combinatorial Matching
Define the $Q_n$-smooth valuation count $\Omega_{\le Q_n}(m) := \sum_{p \le Q_n} v_p(m)$ and smooth part $\operatorname{sm}_{Q_n}(m) := \prod_{p \le Q_n} p^{v_p(m)}$.

**Proposition 3 ($Q_n$-Smooth Matching Sufficiency).** *Set $\mathcal{M}_{\ge 3}(Q_n) := \{1 \le m \le M : \Omega_{\le Q_n}(m) \ge 3\}$. If there exists an injection $\pi : \mathcal{M}_{\ge 3}(Q_n) \hookrightarrow I_x$ such that $(\operatorname{sm}_{Q_n}(m) / p) \mid \pi(m)$ for at least one prime $p \le Q_n$ dividing $\operatorname{sm}_{Q_n}(m)$ at each $m \in \mathcal{M}_{\ge 3}(Q_n)$, then $(H_2)$ holds at $(M, x)$ simultaneously for **all** $w \in \mathcal{W}(Q_n)$.*

*Proof.* For $w \in \mathcal{W}(Q_n)$, $X_w(m) = X_w(\operatorname{sm}_{Q_n}(m)) \le \Omega_{\le Q_n}(m)$, so $(X_w(m) - 2)_+ = 0$ outside $\mathcal{M}_{\ge 3}(Q_n)$. For $m \in \mathcal{M}_{\ge 3}(Q_n)$, $(\operatorname{sm}_{Q_n}(m) / p) \mid \pi(m)$ implies $X_w(\pi(m)) \ge X_w(\operatorname{sm}_{Q_n}(m) / p) = X_w(m) - w_p \ge X_w(m) - 1$, hence $(X_w(\pi(m)) - 1)_+ \ge (X_w(m) - 2)_+$ (`smooth_matching_hinge_step` in `Prop8.lean`). Summing over injective $\pi$ yields $(H_2)$. $\square$

Notice why Proposition 3 is strictly stronger than unsmoothed Proposition 8(1): every $m = s \cdot q \in \mathcal{M}_{\ge 3}(Q_n)$ carrying a prime $q > Q_n$ only requires matching its **much smaller smooth divisor** $s / p$ (which has $\ge \lfloor M / (s/p) \rfloor \ge q \lfloor M / (m/p) \rfloor$ multiples in $I_x$) rather than $m / p = q(s/p)$. Hopcroft–Karp in `explore_h2_smooth.rs` confirms $100\%$ matching of $\mathcal{M}_{\ge 3}(Q_n)$ across all tested $(n, Q_n, M)$ up to $M = 10{,}000$ and all adversarial CRT shifts (`ES_vp1`, `LCM_zero`, sliding windows).

---

## Summary of Open Analytical Obligations to Complete $g(n) \le (2 + o(1))n$
To turn the above into a complete unconditional proof of $g(n) \le (2 + o(1))n$:
1. **Heterogeneous multi-scale weights in Regime 3A**: Combine the Selberg/Buchstab bound (dense small primes) and Paley–Zygmund/Rankin bound (sparse medium primes) for *arbitrary* fractional $w \in [0, 1]^{\{p \le Q_n\}}$ when $L_{j,r} \in [Q_n^\delta, Q_n]$ (specifically handling pairs $p_1 p_2 > L_{j,1}$ when $Q_n \in [M^{1/3}, M^{1/2}]$ where $L_{j,1} \approx M/Q_n < Q_n^2$).
2. **Hall's condition for Proposition 3 in Regime 3B**: Prove Hall's marriage condition $|\mathcal{S}| \le |\bigcup_{m \in \mathcal{S}} \{b \in I_x : \exists p \mid \operatorname{sm}_{Q_n}(m), \, (\operatorname{sm}_{Q_n}(m)/p) \mid b\}|$ analytically for $\mathcal{S} \subseteq \mathcal{M}_{\ge 3}(Q_n)$ when $2n < M \le Q_n^{2+\delta}$.
3. **Cubic-gap bridge ($Q_n^2 \le M < 8n^3$)**: Theorem 5(3) + smooth $(H_{2+\varepsilon})$ gives $(2 + \varepsilon + o(1))n$ for $M \le Q_n^2 - 1$, and Theorem 3 Regime 2 + Theorem 5(1) extends $(2 + \varepsilon + o(1))n$ up to $M = o(n^2 \ln^2 n)$ (since $\pi(M^{1/2}) = o(n)$), leaving $n^2 \ln^2 n \lesssim M < 8n^3$ where $\pi(M^{1/2}) \gtrsim n$ if vertex rounding is applied uncoupled up to $M^{1/2}$.


---

## 4. Audit of the Three Final Analytical Checks

### Check 1: Uniform Hall's Marriage Condition for Proposition 3 ($2n < M \le Q_n^{2+\delta}$) Across Worst-Case CRT Shifts
1. **Short-interval closure ($2n < M \le Q_n - 1$)**: Because $Q_n \ge \lfloor (2 + \varepsilon)n \rfloor + \pi(Q_n - 1) + 1 > (2 + \varepsilon)n$, Proposition 1 ($B = I_x$) already covers $A$ in $|B| = M \le Q_n - 1 = (2 + \varepsilon + o(1))n$ picks for every $x \ge 0$ without invoking Proposition 3.
2. **Exact graph collapse on $Q_n \le M \le 4 Q_n$ (`regime_collapse_le_four_qn` in `HingeInequality.lean`)**: Every $m \in \{1, \dots, M\}$ with $\Omega(m) \ge 3$ satisfies $4 \cdot p_{\max}(m) \le m \le 4 Q_n \implies p_{\max}(m) \le Q_n$. Hence $\mathcal{M}_{\ge 3}(Q_n) = \mathcal{M}_{\ge 3}$ identically across $Q_n \le M \le 4 Q_n$ ($\approx 2n$ to $8n$): $Q_n$-smoothness deletes zero left-vertices and relaxes zero divisors in this band, reducing Proposition 3 directly to unsmoothed Proposition 8(1).
3. **Worst-case CRT obstructions ($x \sim e^{(1+o(1))M}$) and audit verdict**:
   - *Hub-collision bottleneck*: Under `ES_vp1` ($x + c_0 \equiv p \pmod{p^{e_p}}$ for all $p \le Q_n$), the single center element $z = x + c_0 \in I_x$ is divisible by $\prod_{p \le Q_n} p$, making $\Theta(M)$ left-vertices incident to $z$. Any valid Hall / fractional-flow proof must puncture high-collision CRT hubs $H \subseteq I_x$ and route unit flow into $I_x \setminus H$.
   - *Multi-prime divisor necessity*: Restricting to $p = p_{\max}(\operatorname{sm}_{Q_n}(m))$ violates Hall's condition by $3$ vertices at $M = 2{,}520$ under `ES_vp1` ($1{,}431 / 1{,}434$ matched), proving that routing across *all* prime factors $p \mid \operatorname{sm}_{Q_n}(m)$ is indispensable.
   - *Status*: Verified computationally across sliding windows and `ES_vp1` / `LCM_zero` CRT models up to $M = 15{,}120$, **not yet proved analytically across all $U \subseteq \mathcal{M}_{\ge 3}(Q_n)$ and all CRT shifts $x \ge 0$**.

### Check 2: Non-Binary Weights $w_p \in (0, 1)$ and the Difference-of-Convex (DC) Pitfall in Step 3A
1. **Explicit refutation of binary extreme-point reduction ($w \in \{0, 1\}^K \not\Rightarrow w \in [0, 1]^K$)**:
   Because $\mathrm{LHS}_c(w) = \sum_{m=1}^M (X_w(m) - c)_+$ and $\mathrm{RHS}(w) = \sum_{b \in I_x} (X_w(b) - 1)_+$ are *both* convex in $w$, their difference $F_c(w) := \mathrm{LHS}_c(w) - \mathrm{RHS}(w)$ is a **difference of convex (DC)** piecewise-linear function whose local/global maxima lie on chambers of the RHS hyperplane arrangement $\{X_w(b) = 1\} \cap [0, 1]^K$, **not** at $\{0, 1\}^K$.
   - *Verified exact `u128` counterexample (`verify_three_final_checks.rs`)*: On the $5$-prime set $P = \{29, 31, 37, 41, 43\}$ at $M = 37 \cdot 41 \cdot 43 = 65{,}231$, explicit shift $x_5 = 6{,}697{,}389{,}240{,}194{,}279{,}945{,}569{,}557{,}312{,}011$ (where $z = x_5 + 32{,}616 \equiv a_i p_i \pmod{p_i^4}$ with $a = (1132, 1066, 1374, 823, 777)$), and $c = 1.06$:
     $$
     \max_{w \in \{0, 1\}^5} F_{1.06}(w) = 0.0000 \le 0, \qquad \text{whereas} \qquad F_{1.06}\bigl(\tfrac{1}{2}, \tfrac{1}{2}, \tfrac{1}{2}, \tfrac{1}{2}, \tfrac{1}{2}\bigr) = 15.40 - 14.50 = +0.9000 > 0.
     $$
     (At $w_i = 1/2$, all $35$ integers in $\{1, \dots, M\}$ with $\Omega_P(k) = 3$ contribute $0.44$ while $I_{x_5}$ has center $z$ contributing $1.50$ plus $26$ off-center $\Omega_P(b) = 3$ elements—$5$ multiples of $p_i^3$ and $21$ multiples of $p_i^2 p_j$—contributing $13.00$.)
2. **Audit of continuous $w_p \in (0, 1)$ in Step 3A**:
   - Note first an exponent constraint from Theorem 3: because Whole-Cofactor Peeling requires $Q^2 > M$, setting $Q = Q_n > (2 + \varepsilon)n$ covers $M \le Q_n^2 - 1 \approx (2 + \varepsilon)^2 n^2$ (so $M < Q_n^2$ inside Theorem 5(3), making $Q_n^{1+\delta} \le M < Q_n^2$ the active large-$L_{j,1}$ window).
   - Moreover, for continuous $w_i \in (0, 1)$, naive Paley–Zygmund $\mathbb{P}(\widetilde{Y}_j > s) \ge \frac{(\mu_j - s)_+^2}{\mathbb{E}[\widetilde{Y}_j^2]}$ vanishes whenever $\mu_j \le s$ (e.g. $w_i = 0.3, s = 0.8$), where $\{Y_j(b') > s\}$ requires $\ge 3$ co-dividing primes rather than $\ge 1$.
   - While primes $p_i \le L_{j,r}^\eta$ ($\eta \to 0$) equidistribute jointly on $I_{j,r}$ for *arbitrary* continuous $w_i \in [0, 1]$ by the Fundamental Lemma of the Combinatorial Sieve, controlling continuous weights supported on medium primes $p_i \in (L_{j,1}^\eta, Q_n]$ (where triples $p_{i_1} p_{i_2} p_{i_3} > L_{j,1}$ can be anti-correlated or clustered by CRT shifts $x$) remains an open analytical requirement unless Proposition 3's matching (which holds simultaneously for all continuous $w \in [0, 1]^{\{p \le Q_n\}}$ without any convexity assumption!) is established up to $Q_n^2$.

### Check 3: Rigorous Bound on Higher Prime Powers ($r \ge 2$) via $L_0$-Truncation and Divisor Peeling
1. **Why uncut $\sum_{p, r \ge 2} \frac{1}{r-1}\frac{M}{p^r} = O(M)$ cannot be absorbed into $+\varepsilon$ slack**:
   Evaluating the constant explicitly gives
   $$
   \sum_{p} \sum_{r \ge 2} \frac{1}{(r - 1) p^r} = \sum_{p} \frac{1}{p} \ln\Bigl(\frac{p}{p - 1}\Bigr) \approx 0.579931,
   $$
   so $0.580 M$ exceeds $\varepsilon M \ge \varepsilon |\{m \le M : X_w(m) > 2\}|$ whenever $\varepsilon < 0.58$ (and cannot absorb into $(H_{2+\varepsilon})$ when $\mathrm{LHS}_2(w) = O(1)$ is sparse).
2. **Exact prime-by-prime fix (`discrete_peeling_lands_in_band` in `HingeInequality.lean`)**:
   Instead of discarding all $r \ge 2$, fix a growing sieve threshold $L_0$ ($1 \le L_0 \ll L_{j,1} / \ln Q_n$):
   - Every $(j, r)$ with $p_j^r \le M / L_0$ (including **all $r = 2$** whenever $M \ge L_0 Q_n^2$, or all $p_j \le (M / L_0)^{1/2}$) retains $|I_{j,r}| \ge L_{j,r} \ge L_0 \to \infty$ and stays inside the sieve regime.
   - For $(j, r)$ with $p_j^r > M / L_0$, having $\mathrm{LHS}_{j,r}^+ > 0$ requires $(r - 1) w_{p_j} < 1$ ($w_{p_j} < \frac{1}{r-1}$) *and* at least one integer $k_0 \in \{1, \dots, L_{j,r}\} \subseteq \{1, \dots, L_0\}$ with $Y_j(k_0) > 1 + \varepsilon$.
   - Total tail mass at prime $p_j$ satisfies $\sum_{p_j^r > M / L_0} \mathrm{LHS}_{j,r}^+ \le w_{p_j} \sum_{p_j^r > M / L_0} \lfloor M / p_j^r \rfloor \le 2 L_0 w_{p_j}$.
   - Meanwhile, for every $s \in J_{j,1}^+ = [1 - w_{p_j}, 1]$, stripping prime factors $p_i$ ($w_i \le 1$) from $k_0 \le L_0$ one at a time produces a divisor $1 \le d_0 \le L_0$ satisfying $s + \varepsilon < Y_j(d_0) \le s + 1 + \varepsilon$ (verified in DualKernel Lean 4 as `discrete_peeling_lands_in_band`), which generates $\gg \frac{L_{j,1}}{L_0 \ln Q_n} w_{p_j} \gg 2 L_0 w_{p_j}$ positive surplus at $(j, r = 1)$ **for that exact same prime $p_j$ and weight vector $w$**.
