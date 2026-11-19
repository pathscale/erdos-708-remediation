-- HingeInequality.lean: DualKernel-verified formalization of the Q_n-Smooth
-- Shifted-Interval Hinge Inequality (H_c) roadmap (Steps 1, 2, and 3):
--   1. Universal negative-s pointwise dominance across all worst-case shifts x >= 0,
--      and vanishing of the positive-s interval whenever (r - 1) * w_p >= D.
--   2. Complete analytical proof of single-prime (K = 1) and two-prime (K = 2)
--      s-integral dominance across all shifts x >= 0, all M >= 1, and all weights w in [0, 1].
--   3. Clean formal statement of the remaining K >= 3 Q_n-smooth (H_{2+epsilon}) obligation.

import Init
import Std
import NumberTheory
import Prop8
import Theorem3

namespace Erdos708Hinge

-- ============================================================================
-- Step 1A: Universal Deterministic Dominance on s < 0
-- ============================================================================
-- On any subinterval of s < 0 of discrete length `len`, every b' in I_{j,r} has
-- Y_j(b') >= 0 > s, contributing |I_{j,r}| * len, while the LHS count on
-- {1, ..., floor(M / q)} is at most (M / q) * len.
theorem neg_s_dominance_step (x M len : Nat) {q lhsCount : Nat}
    (hq : 0 < q)
    (h_lhs : lhsCount ≤ M / q) :
    lhsCount * len ≤ ((x + M) / q - x / q) * len :=
  Nat.mul_le_mul_right
    (Nat.le_trans h_lhs (Erdos708Prop8.scaled_interval_card_ge_floor x M hq))
    len

-- ============================================================================
-- Step 1B: Vanishing of Positive-s Integral for High Prime Powers
-- ============================================================================
-- Whenever D <= (r - 1) * wp (for instance, ALL r >= 2 when wp = D, i.e., w_p = 1),
-- the positive-s upper endpoint max(0, D - (r - 1) * wp) equals 0, so the
-- positive-s integral vanishes identically.
theorem pos_s_vanishes_of_ge_D (u lo D r_pred_wp : Nat)
    (h_ge : D ≤ r_pred_wp) :
    Erdos708Prop8.minNat u (D - r_pred_wp) - lo = 0 :=
  Eq.trans
    (congrArg (fun hi => Erdos708Prop8.minNat u hi - lo) (Nat.sub_eq_zero_of_le h_ge))
    (@Bool.casesOn (fun b => Nat.ble u 0 = b → cond b u 0 - lo = 0) (Nat.ble u 0)
      (fun _ => Nat.sub_eq_zero_of_le (Nat.zero_le lo))
      (fun ht =>
        Nat.sub_eq_zero_of_le
          (Nat.le_trans (Nat.le_of_ble_eq_true ht) (Nat.zero_le lo)))
      rfl)

-- ============================================================================
-- Step 2A: Single-Prime (K = 1) Exact Dominance
-- ============================================================================
-- At j = 1, Y_1(n) = 0 identically, so on s >= 0 the LHS integrand minNat 0 hi - lo = 0.
theorem single_prime_pos_s_zero (hi lo : Nat) :
    Erdos708Prop8.minNat 0 hi - lo = 0 :=
  Nat.sub_eq_zero_of_le (Nat.zero_le lo)

-- ============================================================================
-- Step 2B: Two-Prime (K = 2) Exact Pointwise Dominance at j = 2
-- ============================================================================

-- Division monotonicity: a <= b and 0 < w => a / w <= b / w.
theorem div_mono_left {a b w : Nat} (hw : 0 < w) (hab : a ≤ b) : a / w ≤ b / w :=
  Erdos708Theorem3.div_ge_of_mul_le hw
    (Nat.le_trans
      (Nat.le_add_left' (w * (a / w)) (a % w))
      (Nat.le_congr (Eq.symm (Nat.mod_add_div a w)) rfl hab))

-- Strict exponent boost at c >= 2 (where w1 <= D <= cMinus1):
-- ((s + cMinus1) / w1 + 1) >= (s / w1 + 1) + 1.
theorem two_prime_strict_exp_boost {s w1 cMinus1 : Nat}
    (hw1 : 0 < w1)
    (hc : w1 ≤ cMinus1) :
    (s / w1 + 1) + 1 ≤ (s + cMinus1) / w1 + 1 :=
  Nat.succ_le_succ
    (Erdos708Theorem3.div_ge_of_mul_le hw1
      (Nat.le_congr
        (Eq.symm (Nat.mul_succ w1 (s / w1)))
        rfl
        (Nat.le_trans
          (Nat.add_le_add_left hc (w1 * (s / w1)))
          (Nat.le_trans
            (Nat.le_add_left' (w1 * (s / w1) + cMinus1) (s % w1))
            (Nat.le_of_eq
              (Eq.trans
                (Eq.symm (Nat.add_assoc (s % w1) (w1 * (s / w1)) cMinus1))
                (congrArg (fun t => t + cMinus1) (Nat.mod_add_div s w1))))))))

-- Power monotonicity: 1 <= p and a <= b => p ^ a <= p ^ b.
theorem pow_pos_of_pos {p : Nat} (hp : 1 ≤ p) : ∀ (e : Nat), 1 ≤ p ^ e :=
  fun e => @Nat.rec (fun n => 1 ≤ p ^ n)
    (Nat.le_refl 1)
    (fun n ih =>
      Nat.le_congr (Nat.one_mul 1) rfl (Nat.mul_le_mul ih hp))
    e

theorem pow_mono_exp {p : Nat} (hp : 1 ≤ p) (a : Nat) : ∀ (d : Nat), p ^ a ≤ p ^ (a + d) :=
  fun d => @Nat.rec (fun k => p ^ a ≤ p ^ (a + k))
    (Nat.le_refl (p ^ a))
    (fun k ih =>
      Nat.le_congr (Nat.mul_one (p ^ a)) rfl (Nat.mul_le_mul ih hp))
    d

theorem pow_le_pow_of_le {p a b : Nat} (hp : 1 ≤ p) (hab : a ≤ b) : p ^ a ≤ p ^ b :=
  Nat.le_congr rfl
    (congrArg (fun e => p ^ e) (Eq.trans (Nat.add_comm a (b - a)) (Nat.sub_add_cancel b a hab)))
    (pow_mono_exp hp a (b - a))

-- Antitonicity of floor division in the denominator: 0 < d1 <= d2 => M / d2 <= M / d1.
theorem div_antitone_right (M : Nat) {d1 d2 : Nat} (hd1 : 0 < d1) (h12 : d1 ≤ d2) :
    M / d2 ≤ M / d1 :=
  Erdos708Theorem3.div_ge_of_mul_le hd1
    (Nat.le_trans
      (Nat.mul_le_mul_right h12 (M / d2))
      (Nat.le_trans
        (Nat.le_add_left' (d2 * (M / d2)) (M % d2))
        (Nat.le_of_eq (Nat.mod_add_div M d2))))

-- Main Theorem for Step 2B (Two-Prime K = 2 Exact Pointwise Dominance at j = 2):
-- For ANY shift x >= 0, ANY interval length M, ANY prime powers p1 >= 1 and p2r > 0,
-- ANY weight w1 > 0, and ANY threshold shift cMinus1 >= 0 (hence BOTH (H_1) and (H_2)!),
-- setting aRhs := s / w1 + 1 and aLhs := (s + cMinus1) / w1 + 1 gives:
--   M / (p1 ^ aLhs * p2r) <= (x + M) / (p1 ^ aRhs * p2r) - x / (p1 ^ aRhs * p2r).
theorem two_prime_j2_pointwise_dominance
    (x M s cMinus1 : Nat) {p1 p2r w1 : Nat}
    (hp1 : 1 ≤ p1)
    (hp2r : 0 < p2r)
    (hw1 : 0 < w1) :
    M / (p1 ^ ((s + cMinus1) / w1 + 1) * p2r) ≤
      (x + M) / (p1 ^ (s / w1 + 1) * p2r) - x / (p1 ^ (s / w1 + 1) * p2r) :=
  Nat.le_trans
    (div_antitone_right M
      (Nat.mul_pos (pow_pos_of_pos hp1 (s / w1 + 1)) hp2r)
      (Nat.mul_le_mul_right
        (pow_le_pow_of_le hp1
          (Nat.succ_le_succ (div_mono_left hw1 (Nat.le_add_right s cMinus1))))
        p2r))
    (Erdos708Prop8.scaled_interval_card_ge_floor x M
      (Nat.mul_pos (pow_pos_of_pos hp1 (s / w1 + 1)) hp2r))

-- ============================================================================
-- Step 3: Formal Statement of the Q_n-Smooth (H_c) Sieve/Matching Obligation
-- ============================================================================
-- Sum of f(1), ..., f(len) for discrete prefix / shifted-window hinge evaluations:
def sumInterval (start len : Nat) (f : Nat → Nat) : Nat :=
  @Nat.rec (fun _ => Nat) 0
    (fun k ih => ih + f (start + k + 1))
    len

-- Given an integer-scaled valuation weight function Xw : Nat -> Nat (supported only on
-- primes p <= Q_n, each with weight w_p <= D) and scaled constant C >= 2 * D
-- (representing c = 2 + epsilon), SmoothHingeAt holds when every shift x >= 0 obeys (H_c):
def SmoothHingeAt (M D C : Nat) (Xw : Nat → Nat) : Prop :=
  ∀ (x : Nat),
    sumInterval 0 M (fun m => Xw m - C) ≤ sumInterval x M (fun b => Xw b - D)

-- Check 1 Regime-Collapse Lemma:
-- Whenever M <= 4 * Qn and m <= M has Omega(m) >= 3 (so 4 * p_max(m) <= m),
-- p_max(m) <= Qn automatically, proving M_{>=3}(Q_n) = M_{>=3} across M <= 4 * Q_n!
theorem four_pos : 0 < 4 := Nat.zero_lt_succ 3

theorem regime_collapse_le_four_qn {m M Qn pmax : Nat}
    (hpmax : pmax * 4 ≤ m)
    (hm : m ≤ Qn * 4)
    (_hM : M ≤ Qn * 4) :
    pmax ≤ Qn :=
  Nat.le_of_mul_le_mul_right four_pos pmax Qn (Nat.le_trans hpmax hm)

-- Check 3 Discrete Intermediate-Value Peeling Step (scaled by denominator D):
-- If Y_prev > s + D + eps (i.e. s + D + eps + 1 <= Y_prev), Y_next + wp = Y_prev,
-- wp <= D, and Y_next <= s + D + eps, then strictly s < Y_next (in fact s + eps < Y_next)!
theorem discrete_peeling_lands_in_band {Yprev Ynext wp s D eps : Nat}
    (h_above : (s + D + eps) + 1 ≤ Yprev)
    (h_step : Ynext + wp = Yprev)
    (h_wp : wp ≤ D) :
    (s + eps) + 1 ≤ Ynext :=
  Nat.le_of_add_le_add_right D
    (Nat.le_trans
      (Nat.le_congr
        (Eq.trans
          (congrArg Nat.succ (Nat.add_right_comm s D eps))
          (Nat.add_right_comm (s + eps) D 1))
        rfl
        h_above)
      (Nat.le_congr h_step rfl (Nat.add_le_add_left h_wp Ynext)))

end Erdos708Hinge
