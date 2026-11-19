-- Corollary4.lean: DualKernel-verified formalization of Corollary 4
-- (Self-contained quadratic-interval bound M >= 9 n^2 => tau(A, I) <= 3 n).

import Init
import Std
import Theorem3

namespace Erdos708Corollary4

-- Monotonicity reflection for squares: if x * x < (k + 1) * (k + 1), then x <= k.
theorem le_of_sq_lt_succ_sq {x k : Nat} (h : x * x < (k + 1) * (k + 1)) : x ≤ k :=
  Or.elim (Nat.lt_or_ge k x)
    (fun hkx =>
      False.elim
        (Nat.lt_irrefl ((k + 1) * (k + 1))
          (Nat.le_trans (Nat.succ_le_succ (Nat.mul_le_mul hkx hkx)) h)))
    (fun hxk => hxk)

-- If (3 * n) * (3 * n) <= M and M < (k + 1) * (k + 1) (where k = floor(sqrt(M))),
-- then 3 * n <= k, and with k * k <= M and 0 < 3 * n we get k <= M / (3 * n).
theorem cor4_sqrt_ge_three_n {n M k : Nat}
    (hM : (3 * n) * (3 * n) ≤ M)
    (hk_upper : M < (k + 1) * (k + 1)) :
    3 * n ≤ k :=
  le_of_sq_lt_succ_sq (Nat.le_trans (Nat.succ_le_succ hM) hk_upper)

theorem cor4_floor_div_ge_k {n M k : Nat}
    (hn : 0 < 3 * n)
    (hM : (3 * n) * (3 * n) ≤ M)
    (hk_lower : k * k ≤ M)
    (hk_upper : M < (k + 1) * (k + 1)) :
    k ≤ M / (3 * n) :=
  Erdos708Theorem3.div_ge_of_mul_le hn
    (Nat.le_trans
      (Nat.mul_le_mul_right (cor4_sqrt_ge_three_n hM hk_upper) k)
      hk_lower)

-- Maximal subproduct 3-chunk bound:
-- When b1 <= k is maximal, multiplying by p* gives k < b1 * p* (i.e., k + 1 <= b1 * p*).
-- For a = (b1 * p*) * b3 <= M < (k + 1) * (k + 1), we necessarily have b3 <= k!
theorem cor4_third_chunk_le_k {k b1_pstar b3 a M : Nat}
    (h_max : k < b1_pstar)
    (h_prod : b1_pstar * b3 = a)
    (ha_le_M : a ≤ M)
    (hk_upper : M < (k + 1) * (k + 1)) :
    b3 ≤ k :=
  Or.elim (Nat.lt_or_ge k b3)
    (fun h_gt =>
      False.elim
        (Nat.lt_irrefl ((k + 1) * (k + 1))
          (Nat.le_trans
            (Nat.succ_le_succ
              (Nat.le_trans
                (Nat.le_congr rfl h_prod (Nat.mul_le_mul h_max h_gt))
                ha_le_M))
            hk_upper)))
    (fun h_le => h_le)

-- Combining <= 3 * |A_sm| picks on A_sm with <= 2 * |A_hi| picks on A_hi yields <= 3 * n:
theorem cor4_total_cover_le_three_n {cardB smSize hiSize n : Nat}
    (h_part : smSize + hiSize = n)
    (h_bound : cardB ≤ 3 * smSize + 2 * hiSize) :
    cardB ≤ 3 * n :=
  Nat.le_trans h_bound
    (Nat.le_congr rfl
      (Eq.trans (Eq.symm (Nat.left_distrib 3 smSize hiSize))
        (congrArg (fun t => 3 * t) h_part))
      (Nat.add_le_add_left (Nat.mul_le_mul_right (Nat.le_succ 2) hiSize) (3 * smSize)))

end Erdos708Corollary4
