#set page(paper: "us-letter", margin: (left: 0.95in, right: 0.95in, top: 0.9in, bottom: 0.9in), numbering: "1")
#set document(title: "Scaled-Interval Hinge Telescoping, Difference-of-Convex Obstructions, and Smooth Proper-Divisor Matching for Erdős Problem 708", author: "C. Bergström")
#set text(font: "Libertinus Serif", size: 10.3pt, hyphenate: false)
#set par(justify: true, leading: 0.62em, spacing: 0.8em)
#set heading(numbering: "1.")
#show heading: set block(above: 1.2em, below: 0.6em, sticky: true)
#show raw.where(block: false): it => text(size: 9.4pt, font: "DejaVu Sans Mono", it.text.replace("_", "_\u{200b}"))

#let pmod(m) = $space ("mod" #m)$
#let ZZ = $bb(Z)$
#let prod = math.product
#let lcm = math.op("lcm")
#let sm = math.op("sm")

#align(center)[
  #set par(justify: false)
  #text(size: 14pt, weight: "bold")[
    Scaled-Interval Hinge Telescoping, \
    Difference-of-Convex Obstructions, and \
    Smooth Proper-Divisor Matching for Erdős Problem 708
  ]
  #v(0.5em)
  #text(size: 11pt, weight: "semibold")[C. Bergström]
  #v(0.15em)
  #text(size: 9.8pt)[24x AI Research]
  #v(0.14em)
  #text(size: 9pt)[ORCID: `0009-0008-7153-1817`]
  #v(0.18em)
  #text(size: 9.5pt)[November 2026]
]

#v(0.65em)
#pad(x: 1.8em)[
  #text(weight: "bold")[Abstract.]
  Erdős Problem 708 asks whether every $n$-element set $A subset.eq ZZ_(>= 2)$ admits a product cover of size $(2 + o(1)) n$ in every shifted block $I_x$. Companion work reduces intervals below $Q_n^2$ to the shifted-interval hinge inequality $(H_c)$ on $Q_n$-smooth prime weights. This paper develops the scaled-interval integral decomposition of $(H_c)$ and isolates the analytical obstructions below coefficient two. Telescoping over scaled intervals $I_(j, r)$ proves deterministic dominance across all negative thresholds and eliminates high prime powers whenever $(r - 1) w_(p_j) >= 1$. Every weight vector supported on at most two primes satisfies $(H_c)$ pointwise across all thresholds $c >= 1$. A five-prime Chinese Remainder witness at $M = 65","231$ satisfies $(H_(1.06))$ on all thirty-two binary vertices while failing at the cube midpoint. That counterexample rules out binary extreme-point reduction. Discrete intermediate-value divisor peeling bounds high prime powers prime by prime, while $Q_n$-smooth proper-divisor matching implies $(H_2)$ across all continuous weights simultaneously. DualKernel verifies $51$ Lean declarations with zero unproven axioms. Three explicit analytical obligations remain open.
]

= Introduction, Obstructions, and Main Results

Pointwise comparison of prime-weighted level sets across a shifted interval $I_x$ fails once interval length reaches $e^(100)$ @hensleyrichards74. Hensley and Richards constructed shifted blocks with $Theta(L / ln^2 L)$ more primes than ${1, dots, L}$, breaking threshold-zero dominance under unit weights. A second failure invalidates binary vertex shortcuts on fractional prime weights. Both sides of the shifted-interval hinge inequality are convex in the weight vector, so their difference can peak strictly inside the unit cube.

Given a finite set $A subset.eq ZZ_(>= 2)$ of size $n$ with maximum $M = max(A)$ and an integer shift $x >= 0$, set $I_x := {x + 1, dots, x + M}$. The minimum product-cover number is
$ tau(A, I_x) := min { |B| : B subset.eq I_x, space prod_(a in A) a divides prod_(b in B) b }. $
Taking the supremum over all $n$-sets and shifts defines $g(n)$ @erdossuranyi59.#footnote[Writing $|B| <= g(n)$ follows Bloom @bloom708 and L. Mazur, since $A = {2, dots, n + 1}$ forces $|B| <= n + 1$.] Explicitly,
$ g(n) := sup { tau(A, I_x) : A subset.eq ZZ_(>= 2), space |A| = n, space M = max(A), space x >= 0 }. $

Erdős and Surányi @erdossuranyi59 proved $g(3) = 4$ and $g(n) >= (2 - o(1)) n$ in 1959 using semiprime cliques centered around one divisible integer. Two later problem papers by Erdős highlighted the conjecture $g(n) <= (2 + o(1)) n$ @erdos92c @erdos95, catalogued as Problem 708 @bloom708. Chen @chen26 established linear upper bounds $g(n) <= 12 n$ in Lean 4 and $g(n) <= 11 n$ via linear-programming hinge duality. The first companion paper @bergstrom26small proved $g(4) = 5$, $g(5) = 6$, and $g(6) = 8$, alongside constructive witnesses for $g(7) >= 9$ and $g(8) >= 11$. Whole-cofactor cumulative-GCD peeling and $Q_n$-smooth extreme-point rounding in the second companion paper @bergstrom26asymptotic lowered the unconditional bound to $g(n) <= (56501 / 6400 + o(1)) n$.

That smooth rounding reduction also showed that $(H_c)$ at $c = 2 + epsilon$ on $Q_n$-smooth weights implies $(2 + epsilon + o(1)) n$ covers below $Q_n^2$. The general asymptotic conjecture remains open. This paper proves four unconditional structural theorems for the $Q_n$-smooth hinge functional and isolates three open analytical obligations. Table 1 summarizes all interval regimes, including the $51$ DualKernel-verified Lean declarations proved here.

#figure(
  table(
    columns: (1.05fr, 1.15fr, 1.35fr),
    inset: (x: 5pt, y: 4pt),
    align: (left, left, left),
    stroke: 0.5pt,
    [*Regime or Object*], [*Proved Bound / Identity*], [*Method and Status*],
    [Small cardinalities $n <= 6$], [$g(4) = 5, space g(5) = 6, space g(6) = 8$], [Certified CRT + slot packing @bergstrom26small],
    [Short intervals $M <= Q_n - 1$], [$tau(A, I_x) <= M < Q_n$], [Full-interval factorial cover @bergstrom26asymptotic],
    [Global unconditional $M >= 2$], [$g(n) <= (56501 / 6400 + o(1)) n$], [Smooth LP rounding + $(H_(56501 / 6400))$ @bergstrom26asymptotic],
    [Quadratic regime $M >= 9 n^2$], [$tau(A, I_x) <= 3 n$], [Whole-cofactor peeling @bergstrom26asymptotic],
    [Cubic regime $M >= 8 n^3$], [$tau(A, I_x) <= 2 n$], [Long-interval prime cover @chen26],
    [Negative slice $s < 0$ and $K <= 2$], [Deterministic $(H_c)$ for all $c >= 1$], [Proposition 1 and Theorem 2 ($31$ Lean decls)],
    [Binary vertex reduction on $[0, 1]^5$], [Refuted at $M = 65","231$, $c = 1.06$], [Proposition 3 interior witness ($+0.90 > 0$)],
    [High prime powers $p_j^r > M / L_0$], [Tail $< 2 L_0 w_(p_j)$ + divisor band], [Theorem 4 discrete divisor peeling (Lean)],
    [Smooth matching $cal(M)_(>= 3) (Q_n) arrow.hook I_x$], [Implies $(H_2)$ on all $w in cal(W) (Q_n)$], [Theorem 5 (verified to $M = 15","120$, open in general)],
  ),
  caption: [Summary of unconditional bounds, structural hinge theorems, and remaining open regimes for Erdős Problem 708.],
)

= Scaled-Interval Telescoping and Two-Prime Pointwise Dominance

This section establishes the exact scaled-interval integral equivalence for $(H_c)$ and resolves all one-prime and two-prime weight vectors unconditionally. Omitting division by $p_j^r$ in the inner domain breaks telescoping whenever higher prime powers divide elements of $I_x$.

Fix $M >= 2$, an integer shift $x >= 0$, and a prime-weight vector $w in [0, 1]^({p <= M})$. Set $(t)_+ := max(t, 0)$. The weighted valuation is
$ X_w (m) := sum_(p <= M) v_p (m) w_p >= 0. $
Given $c >= 1$, the deterministic shifted-interval hinge inequality $(H_c)$ at $(M, x, w)$ states
$ sum_(m = 1)^M (X_w (m) - c)_+ <= sum_(b in I_x) (X_w (b) - 1)_+. $
Order the active primes $p_1 < dots < p_K <= M$ carrying positive weight. Define the prefix valuation sum by $Y_1 (u) := 0$ and
$ Y_j (u) := sum_(i = 1)^(j - 1) v_(p_i) (u) w_(p_i) quad (2 <= j <= K). $
For each active prime $p_j$ and positive exponent $r$, put $L_(j, r) := floor(M / p_j^r)$. The corresponding scaled block is
$ I_(j, r) := { floor(x / p_j^r) + 1, dots, floor((x + M) / p_j^r) }, quad |I_(j, r)| in { L_(j, r), space L_(j, r) + 1 }. $

*Proposition 1 (Scaled-Interval Hinge Equivalence and Negative-$s$ Dominance).* Fix $c >= 1$, $M >= 2$, $x >= 0$, and $w in [0, 1]^({p <= M})$.

1. _(Scaled-interval integral equivalence)_. Every real $u$ and $a <= b$ satisfy $(u - a)_+ - (u - b)_+ = integral_a^b bold(1)_(u > t) dif t = (min(u, b) - a)_+$. Thus $(H_c)$ holds at $(M, x, w)$ if and only if
  $ sum_(j = 1)^K sum_(r >= 1) sum_(k = 1)^(L_(j, r)) integral_(1 - r w_(p_j))^(1 - (r - 1) w_(p_j)) bold(1)_(Y_j (k) > s + c - 1) dif s <= sum_(j = 1)^K sum_(r >= 1) sum_(b' in I_(j, r)) integral_(1 - r w_(p_j))^(1 - (r - 1) w_(p_j)) bold(1)_(Y_j (b') > s) dif s. $

2. _(Negative-$s$ dominance and high-power vanishing)_. Every negative threshold $s < 0$, active index $j$, and positive exponent $r$ satisfy the bound below.
  $ sum_(k = 1)^(L_(j, r)) bold(1)_(Y_j (k) > s + c - 1) <= L_(j, r) <= |I_(j, r)| = sum_(b' in I_(j, r)) bold(1)_(Y_j (b') > s). $

  Pairs $(j, r)$ with $p_j^r > M$ or $(r - 1) w_(p_j) >= 1$ therefore satisfy deterministic dominance across their full integration domain.

_Proof._ Coprimality $gcd(p_i, p_j) = 1$ for $i < j$ ensures $Y_j (p_j^r k) = Y_j (k)$ across all positive integers $r$ and $k$. Telescoping the single-prime increments across $j = 1, dots, K$ recovers $(X_w (u) - c_0)_+$. Expanding each increment over $1 <= r <= v_(p_j) (u)$ maps multiples of $p_j^r$ in ${1, dots, M}$ bijectively onto ${1, dots, L_(j, r)}$. Multiples of $p_j^r$ in $I_x$ map bijectively onto $I_(j, r)$, and shifting the integration variable gives Part (1).

When $s < 0$, non-negativity $Y_j (b') >= 0 > s$ sets every indicator on $I_(j, r)$ equal to one, while $|I_(j, r)| >= L_(j, r)$ bounds the left sum. Whenever $p_j^r > M$, the left sum has $L_(j, r) = 0$ terms. If $(r - 1) w_(p_j) >= 1$, the upper endpoint $1 - (r - 1) w_(p_j)$ is non-positive, placing the entire domain inside $(-infinity, 0]$. $square$

Unit weights $w_(p_j) = 1$ satisfy $(r - 1) w_(p_j) >= 1$ for every $r >= 2$. Binary weights therefore eliminate all higher prime-power contributions on the positive-$s$ axis automatically.

*Theorem 2 (Unconditional Pointwise Dominance for Two Active Primes).* Let $w in [0, 1]^({p <= M})$ be supported on at most two distinct primes. Across every $c >= 1$, every $M >= 2$, and every $x >= 0$ (with $M = 1$ holding vacuously), the integrand in Proposition 1(1) satisfies pointwise dominance at every $(j, r, s)$.

_Proof._ Proposition 1(2) resolves every $s < 0$. Consider $s >= 0$. At $j = 1$, the prefix sum $Y_1$ vanishes identically, so both indicators equal zero. For $j = 2$ with $w_1 := w_(p_1) in (0, 1]$, define the integer exponent threshold.
$ a(t) := floor(t / w_1) + 1 >= 1 quad (t >= 0). $
Because $Y_2 (u) = w_1 v_(p_1) (u)$, the strict bound $Y_2 (u) > t$ holds exactly when $p_1^(a(t))$ divides $u$. Nested floor division on ${1, dots, L_(2, r)}$ evaluates the left count.
$ sum_(k = 1)^(L_(2, r)) bold(1)_(Y_2 (k) > s + c - 1) = floor(L_(2, r) / p_1^(a(s + c - 1))) = floor(M / (p_1^(a(s + c - 1)) p_2^r)). $
An integer $b'$ lies in $I_(2, r)$ with $p_1^(a(s)) divides b'$ precisely when $p_2^r b'$ lies in $I_x$ and is divisible by $p_1^(a(s)) p_2^r$. Counting multiples in $I_x$ bounds the right count.
$ sum_(b' in I_(2, r)) bold(1)_(Y_2 (b') > s) = |I_x inter p_1^(a(s)) p_2^r ZZ| >= floor(M / (p_1^(a(s)) p_2^r)). $

Monotonicity $s + c - 1 >= s$ for $c >= 1$ implies $a(s + c - 1) >= a(s)$ (with strict boost $a(s + c - 1) >= a(s) + 1$ at $c >= 2$), proving pointwise dominance. $square$

Theorem 2 explains why $(H_1)$ holds universally on two primes. Erdős and Surányi's lower bound $g(3) = 4 > 3$ therefore requires at least three active primes. On ${5, 7, 11}$ at $M = 77$, shift $x = 1","127$ violates $(H_1)$ by $-1$ while satisfying $(H_2)$ with surplus $+7$.

= Difference-of-Convex Non-Convexity and High Prime Powers

Extending $(H_c)$ beyond two active primes encounters two analytical pitfalls on fractional weights $w_p in (0, 1)$. On five primes ${29, 31, 37, 41, 43}$ at $M = 65","231$, every binary vertex satisfies $(H_(1.06))$ while the cube midpoint violates it by $+0.90$.

Fix $(M, x, c)$ and consider the hinge difference functional on $[0, 1]^K$.
$ F_c (w) := sum_(m = 1)^M (X_w (m) - c)_+ - sum_(b in I_x) (X_w (b) - 1)_+. $
Each summand is convex and piecewise linear in $w$. Subtracting two convex functions produces a difference-of-convex objective whose maxima lie on chambers of ${X_w (b) = 1}$ rather than on ${0, 1}^K$.

*Proposition 3 (Interior Violation of Binary Vertex Reduction).* Set $P = {29, 31, 37, 41, 43}$ and $M = 37 dot 41 dot 43 = 65","231$. Let $x_5 = 6","697","389","240","194","279","945","569","557","312","011$, constructed via the Chinese Remainder Theorem so that $z := x_5 + 32","616$ satisfies $z equiv a_i p_i pmod(p_i^4)$ for $(a_1, dots, a_5) = (1132, 1066, 1374, 823, 777)$. Threshold $c = 1.06$ separates the binary vertices from $w_* := (1 / 2, 1 / 2, 1 / 2, 1 / 2, 1 / 2)$.
$ max_(w in {0, 1}^5) F_(1.06) (w) = 0, quad F_(1.06) (w_*) = +0.90 > 0. $

_Proof._ Every integer $k <= M$ satisfies $Omega_P (k) <= 3$ because $29^4 = 707","281 > M$. Exactly $35$ integers in ${1, dots, M}$ satisfy $Omega_P (k) = 3$ ($10$ squarefree triples, $3$ cubes, and $22$ products $p_i^2 p_j$). At $w_*$, integers with $Omega_P (k) <= 2$ satisfy $X_(w_*) (k) <= 1 < 1.06$. Each three-factor integer contributes $0.44$, giving a left sum of $15.40$.

Inside $I_(x_5) = {z - 32","615, dots, z + 32","615}$, the center $z$ has valuation $(1, 1, 1, 1, 1)$ and contributes $1.50$. Every semiprime in $I_(x_5) without {z}$ sits on the kink $X_(w_*) (b) = 1$ and contributes zero. Because $p_i divides z$ for every $p_i in P$, any prime $p_i$ dividing $z + d$ also divides $d$. Since $29 dot 31 dot 37 = 33","263 > 32","615$, no off-center element has three distinct prime factors in $P$. Direct division confirms $v_(p_i) (b) <= 3$ across $I_(x_5)$, with exactly $26$ off-center elements having $Omega_P (b) = 3$ ($5$ multiples of $p_i^3$ and $21$ multiples of $p_i^2 p_j$). Those $26$ elements contribute $13.00$, giving a right sum of $14.50$ and $F_(1.06) (w_*) = +0.90$, whereas all $32$ binary vectors satisfy $F_(1.06) (w) <= 0$. $square$

Fractional weights also activate exponents $r >= 2$ on the positive-$s$ interval $J_(j, r)^+ := [1 - r w_(p_j), 1 - (r - 1) w_(p_j)] inter [0, 1]$ whenever $(r - 1) w_(p_j) < 1$. Define the positive-$s$ left slice integral at $(j, r)$ as follows.
$ "LHS"_(j, r)^+ := sum_(k = 1)^(L_(j, r)) integral_(J_(j, r)^+) bold(1)_(Y_j (k) > s + c - 1) dif s <= w_(p_j) L_(j, r). $
Bounding $J_(j, r)^+$ naively by its width across all $r >= 2$ yields a linear constant exceeding $epsilon M$ for small $epsilon > 0$. Truncating at scale $L_0 >= 1$ and peeling prime factors from witnesses below $L_0$ bounds these tails prime by prime.

*Theorem 4 (Discrete Intermediate-Value Divisor Peeling for High Prime Powers).* Fix $epsilon > 0$, $c = 2 + epsilon$, $M >= 2$, $x >= 0$, and $w in [0, 1]^({p <= M})$.

1. _(Uncut series constant)_. Summing $(r - 1)^(-1) p^(-r)$ across all primes $p >= 2$ and exponents $r >= 2$ evaluates in closed form.
  $ sum_(p >= 2) sum_(r >= 2) frac(1, (r - 1) p^r) = sum_(p >= 2) frac(1, p) ln (frac(p, p - 1)) approx 0.579931. $

2. _(Prime-by-prime $L_0$-truncation)_. Fix any integer cutoff $L_0 >= 1$. Every $(j, r)$ with $p_j^r > M / L_0$ and $"LHS"_(j, r)^+ > 0$ satisfies $(r - 1) w_(p_j) < 1$, $L_(j, r) < L_0$, and the tail bound.
  $ sum_(r >= 2, space p_j^r > M / L_0) "LHS"_(j, r)^+ <= w_(p_j) sum_(r >= 2, space p_j^r > M / L_0) floor(M / p_j^r) < 2 L_0 w_(p_j). $

3. _(Constructive divisor peeling)_. Whenever $k_0 in {1, dots, L_0}$ satisfies $Y_j (k_0) > 1 + epsilon$, every $s in [0, 1]$ admits a divisor $d_0 divides k_0$ ($1 <= d_0 <= L_0$) landing in the target band.
  $ s + epsilon < Y_j (d_0) <= s + 1 + epsilon. $

_Proof._ Substituting $m = r - 1$ into $-ln(1 - 1 / p) = sum_(m >= 1) 1 / (m p^m)$ gives Part (1). In Part (2), Proposition 1 implies $J_(j, r)^+ != emptyset$ and hence $(r - 1) w_(p_j) < 1$. Geometric decay $floor(M / p_j^(r_0 + t)) <= (L_0 - 1) / 2^t$ from the first exponent above $M / L_0$ bounds the sum below $2 L_0 w_(p_j)$.

For Part (3), factor $k_0 = q_1 dots.c q_t$ into primes and form the prefix divisors $d_m := q_1 dots.c q_m$ for $0 <= m <= t$. Each step increases $Y_j$ by at most one because $w_p <= 1$. Since $Y_j (d_0) = 0$ while $Y_j (d_t) > 1 + epsilon >= s + epsilon$, the smallest index $m$ with $Y_j (d_m) > s + epsilon$ satisfies $Y_j (d_m) <= Y_j (d_(m - 1)) + 1 <= s + 1 + epsilon$. $square$

Multiples $k = d_0 u <= L_(j, 1)$ with $u$ coprime to $p_1 dots.c p_(j - 1) d_0$ preserve $Y_j (d_0 u) = Y_j (d_0)$. Those multiples supply $gt.double (L_(j, 1) / (L_0 ln Q_n)) w_(p_j)$ complementary slots at $r = 1$ whenever $L_0^2 ln Q_n = o(L_(j, 1))$.

= Smooth Proper-Divisor Matching and Asymptotic Sieve Regimes

Combinatorial matching on $Q_n$-smooth parts bypasses difference-of-convex non-convexity across all continuous dual weights simultaneously. Replacing an integer $m$ by its $Q_n$-smooth part shrinks each required proper divisor whenever a prime above $Q_n$ divides $m$.

Let $cal(W) (Q_n)$ denote the cube of $Q_n$-smooth prime weights vanishing above $Q_n$. Define the smooth valuation count, smooth part, and three-factor set as follows.
$ Omega_(<= Q_n) (m) := sum_(p <= Q_n) v_p (m), quad sm_(Q_n) (m) := prod_(p <= Q_n) p^(v_p (m)), quad cal(M)_(>= 3) (Q_n) := {1 <= m <= M : Omega_(<= Q_n) (m) >= 3}. $

*Theorem 5 ($Q_n$-Smooth Matching Sufficiency, Graph Collapse, and Sieve Bounds).* Fix $Q_n >= 2$, $M >= 2$, and $x >= 0$.

1. _(Smooth matching sufficiency)_. Suppose an injection $pi : cal(M)_(>= 3) (Q_n) arrow.hook I_x$ satisfies $(sm_(Q_n)(m) slash p) divides pi(m)$ for some prime $p <= Q_n$ dividing $sm_(Q_n)(m)$ at each $m in cal(M)_(>= 3) (Q_n)$. Then $(H_2)$ holds at $(M, x, w)$ simultaneously across all continuous $w in cal(W) (Q_n)$.

2. _(Graph collapse up to $4 Q_n$)_. Across $Q_n <= M <= 4 Q_n$, every integer $m <= M$ with $Omega(m) >= 3$ satisfies $p_"max" (m) <= M / 4 <= Q_n$, so $cal(M)_(>= 3) (Q_n) = cal(M)_(>= 3)$ identically.

3. _(Binary smooth sieve bounds)_. Fix $delta > 0$ and binary weights $w = bold(1)_S$ for $S subset.eq {p <= Q_n}$ at index $j$ with $L := L_(j, 1) >= Q_n^(1 + delta)$. Write $S_(< j) := S inter {p_1, dots, p_(j - 1)}$ and $mu_j := sum_(p in S_(< j)) 1 / p$.

   _(a) Dense harmonic sums ($mu_j -> infinity$)_. Selberg's upper sieve @halberstamrichert74 bounds coprime survivors on $I_(j, 1)$ uniformly in $x >= 0$. Semiprimes $k = p q <= L$ with $p in S_(< j)$ below $L^(delta / (2 + 2 delta))$ and prime $q in [p_j, L / p]$ gain a factor $mu_j$. That extra factor dominates $(H_2)$ once $mu_j$ exceeds an absolute constant.

   _(b) Sparse harmonic sums ($0 < mu_j < 1$ with $S_(< j) subset.eq {p <= L^(1 / 2 - theta)}$)_. Second-moment Cauchy–Schwarz on $I_(j, 1)$ gives $|{b' in I_(j, 1) : Y_j (b') >= 1}| >= (1 - o(1)) frac(mu_j, 1 + mu_j) L$ uniformly in $x >= 0$. That lower bound strictly exceeds the pair union bound $frac(1, 2) (mu_j^2 + sum_(p in S_(< j)) p^(-2)) L$.

_Proof._ Every $w in cal(W) (Q_n)$ obeys $X_w (m) <= Omega_(<= Q_n) (m)$, so $(X_w (m) - 2)_+ = 0$ outside $cal(M)_(>= 3) (Q_n)$. Divisibility $(sm_(Q_n)(m) slash p) divides pi(m)$ gives $X_w (pi(m)) >= X_w (m) - w_p >= X_w (m) - 1$. Summing $(X_w (pi(m)) - 1)_+ >= (X_w (m) - 2)_+$ over the injective image proves Part (1).

Writing $m = p_"max" (m) u$ with $Omega(u) >= 2$ forces $u >= 4$ and $p_"max" (m) <= M / 4 <= Q_n$, proving Part (2). In Part (3)(a), Selberg's sieve on $I_(j, 1)$ pairs with the open prime interval $[p_j, L / p]$ created by $p_j <= L^(1 / (1 + delta))$. Under Part (3)(b), $S_(< j) subset.eq {p <= L^(1 / 2 - theta)}$ implies $|S_(< j)|^2 <= L^(1 - 2 theta) = o(L)$, so off-diagonal rounding errors in $sum_(b' in I_(j, 1)) N(b')^2$ total $O(|S_(< j)|^2) = o(L)$. Cauchy–Schwarz then closes via $frac(1, 2) mu_j (1 + mu_j) < 1$ on $(0, 1)$. $square$

= Formal Verification and Open Analytical Obligations

Formal kernel checking and adversarial stress tests separate the proved theorems above from three open analytical problems required to resolve $g(n) <= (2 + o(1)) n$. DualKernel audits all $51$ Lean declarations across five formalization modules with zero unproven axioms. Table 2 records the verified counts across all proof components and computational stress suites, including $44","800$ two-prime configurations with zero deficit.

#figure(
  table(
    columns: (1.2fr, auto, 1.25fr),
    inset: (x: 5pt, y: 4pt),
    align: (left, right, left),
    stroke: 0.5pt,
    [*Verified Component*], [*Recorded Metric*], [*Verification Basis*],
    [Formal Lean 4 theorems across $5$ files], [$51$ decls ($0$ `sorry`)], [DualKernel independent typecheck],
    [Two-prime $(H_1)$ and $(H_2)$ grid checks], [$44","800$ instances], [Minimum surplus $0.000000$ (Theorem 2)],
    [Five-prime DC counterexample ($M = 65","231$)], [$0.00$ vs $+0.90$], [All $32$ binary vertices vs $w_* = (1 / 2)^5$],
    [Uncut $r >= 2$ series coefficient], [$0.579931 M$], [Exceeds $epsilon M$ for all $epsilon < 0.579$],
    [Discrete divisor-peeling band checks], [$2","530$ pairs], [$100%$ land in $(s, s + 1 + epsilon]$ (Theorem 4)],
    [Smooth Hopcroft–Karp CRT matchings], [Up to $M = 15","120$], [$100%$ matched ($1","728$ of $1","728$ at $n = 500$)],
    [Continuous coordinate-ascent ($Q_n = 40, M = 2","500$)], [$"max" F_2 = 0.000000$], [$5$ initializations under centered CRT],
  ),
  caption: [Summary of DualKernel formal verification counts and standalone computational checks.],
)

Completing an unconditional proof of $g(n) <= (2 + o(1)) n$ via this architecture requires closing three explicit analytical obligations.

1. *Uniform Hall condition for smooth matching ($Q_n <= M <= Q_n^(2 + delta)$)*. Theorem 5(1) requires proving $|N_(I_x) (U)| >= |U|$ analytically across all subsets $U subset.eq cal(M)_(>= 3) (Q_n)$ and all Chinese Remainder shifts $x >= 0$ by puncturing high-multiplicity hubs in $I_x$.

2. *Continuous multi-scale weights on medium primes ($M > Q_n^(1 + delta)$)*. Because Proposition 3 rules out binary vertex reduction, extending Theorem 5(3) requires controlling arbitrary fractional weights $w_p in (0, 1)$ supported on medium primes $p in (L_(j, 1)^eta, Q_n]$ where prime triples exceed $L_(j, 1)$.

3. *Quadratic-to-cubic interval bridge ($Q_n^2 <= M < 8 n^3$)*. Smooth rank rounding @bergstrom26asymptotic reduces $M <= Q_n^2 - 1$ to smooth $(H_(2 + epsilon))$, while $M >= 9 n^2$ yields $3 n$ @bergstrom26asymptotic and $M >= 8 n^3$ yields $2 n$ @chen26. Closing the intermediate band $n^2 ln^2 n lt.approx M < 8 n^3$ at coefficient two remains open.

#set heading(numbering: none)

= Data and Code Availability

Five Lean 4 formalization modules ($51$ declarations verified by DualKernel) and three zero-dependency Rust verifiers are archived at Zenodo @bergstrom26smoothcode (`https://doi.org/10.5281/zenodo.24366998`) alongside the companion archives @bergstrom26small @bergstrom26asymptotic.
#[
  #set par(justify: false)
  - Scaled-interval $s$-integral verifier ($3","174$ bytes) has SHA-256 digest \ `05ec9b8d6e30a0d987d3319387955a2d19e5b88a7bd796445944894fda6a2ad3`.
  - Smooth matching and sieve explorer ($27","202$ bytes) has SHA-256 digest \ `48add0a21fd8869f5e66f45114fd48e219bc0f7ebf1b7b527a30362bc3c86fc0`.
  - Analytical checks and DC counterexample verifier ($17","038$ bytes) has SHA-256 digest \ `84b59b9b7093c0ef1982088eaee9dc5a79140d54a5785586da5bd2c3e2a10e92`.
]

= Acknowledgments and Declaration of Generative AI

The author used internal research automation (Karen, 24x AI Research) and Google Gemini during counterexample search, Lean 4 formalization, verifier implementation, and manuscript editing. Every proof and computation was subsequently reviewed, verified, and edited by the author, who assumes full responsibility for the mathematical content.

#bibliography("references.bib", title: "References")
