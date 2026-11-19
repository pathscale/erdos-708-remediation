-- Theorem3.lean: DualKernel-verified formalization of Lemma 2 (Incremental Cumulative-GCD
-- Extension) and Theorem 3 (Whole-Cofactor Peeling Budget & Regimes 1 and 2).

import Init
import Std
import NumberTheory
import Prop8

namespace Erdos708Theorem3

-- Divisibility relation over Nat: g * L = H0 * h, L | P, g | b => H0 * h | b * P.
theorem mul_four_rearrange (g v L u : Nat) :
    (g * v) * (L * u) = (g * L) * (v * u) :=
  Eq.trans (Nat.mul_assoc g v (L * u))
    (Eq.trans
      (congrArg (fun t => g * t)
        (Eq.trans (Eq.symm (Nat.mul_assoc v L u))
          (Eq.trans (congrArg (fun s => s * u) (Nat.mul_comm v L))
            (Nat.mul_assoc L v u))))
      (Eq.symm (Nat.mul_assoc g L (v * u))))

theorem lemma2_lcm_gcd_dvd {H0 h g L P b : Nat}
    (h_id : H0 * h = g * L)
    (hL : L ∣ P)
    (hg : g ∣ b) :
    (H0 * h) ∣ (b * P) :=
  Exists.elim hL (fun u hu =>
    Exists.elim hg (fun v hv =>
      Exists.intro (v * u)
        (Eq.trans
          (congrArg (fun x => x * P) hv)
          (Eq.trans
            (congrArg (fun y => (g * v) * y) hu)
            (Eq.trans (mul_four_rearrange g v L u)
              (congrArg (fun z => z * (v * u)) (Eq.symm h_id)))))))

-- Floor division lower bound: 0 < g and g * k <= M implies k <= M / g.
theorem div_ge_of_mul_le {g k M : Nat} (hg : 0 < g) (h : g * k ≤ M) : k ≤ M / g :=
  Or.elim (Nat.lt_or_ge (M / g) k)
    (fun hlt =>
      False.elim
        (Nat.not_succ_le_self M
          (Nat.le_trans
            (Nat.le_congr
              (congrArg Nat.succ (Nat.mod_add_div M g))
              (Eq.symm (Nat.mul_succ g (M / g)))
              (Nat.le_congr
                (Eq.symm (Nat.add_right_comm (M % g) (g * (M / g)) 1))
                (Nat.add_comm g (g * (M / g)))
                (Nat.add_le_add_right (Nat.mod_lt M hg) (g * (M / g)))))
            (Nat.le_trans (Nat.mul_le_mul_left hlt g) h))))
    (fun hge => hge)

-- Lemma 2 Pigeonhole Supply Count:
-- When g * (cardB0 + 1) <= M and 0 < g, the interval I = [x+1, x+M] contains at least
-- cardB0 + 1 multiples of g, guaranteeing an untouched multiple in I \ B0.
theorem lemma2_pigeonhole_supply (x : Nat) {M g cardB0 : Nat}
    (hg : 0 < g)
    (h_budget : g * (cardB0 + 1) ≤ M) :
    cardB0 + 1 ≤ (x + M) / g - x / g :=
  Nat.le_trans
    (div_ge_of_mul_le hg h_budget)
    (Erdos708Prop8.scaled_interval_card_ge_floor x M hg)

-- Theorem 3 Peeling Step-Count Identity & Strict Saving:
-- Step 1 adds r picks, Step 2 adds <= hiSize - r picks, Step 3 adds hiSize - r picks.
-- Total added picks: r + ((hiSize - r) + (hiSize - r)) = (hiSize + hiSize) - r.
theorem peel_steps_sum {hiSize r : Nat} (hr : r ≤ hiSize) :
    r + ((hiSize - r) + (hiSize - r)) = (hiSize + hiSize) - r :=
  Nat.add_right_cancel
    (Eq.trans
      (Nat.add_assoc r ((hiSize - r) + (hiSize - r)) r)
      (Eq.trans
        (congrArg (fun t => r + t)
          (Eq.trans (Nat.add_assoc (hiSize - r) (hiSize - r) r)
            (congrArg (fun s => (hiSize - r) + s) (Nat.sub_add_cancel hiSize r hr))))
        (Eq.trans
          (Eq.symm (Nat.add_assoc r (hiSize - r) hiSize))
          (Eq.trans
            (congrArg (fun t => t + hiSize)
              (Eq.trans (Nat.add_comm r (hiSize - r)) (Nat.sub_add_cancel hiSize r hr)))
            (Eq.symm
              (Nat.sub_add_cancel (hiSize + hiSize) r
                (Nat.le_trans hr (Nat.le_add_right hiSize hiSize))))))))

theorem theorem3_peeling_strict_saving {smSize hiSize r : Nat}
    (hr_pos : 1 ≤ r) (hr_le : r ≤ hiSize) :
    smSize + (r + ((hiSize - r) + (hiSize - r))) ≤ (smSize + (hiSize + hiSize)) - 1 :=
  Nat.le_trans
    (Nat.le_of_eq
      (Eq.trans
        (congrArg (fun t => smSize + t) (peel_steps_sum hr_le))
        (Nat.add_right_cancel
          (Eq.trans
            (Nat.add_assoc smSize ((hiSize + hiSize) - r) r)
            (Eq.trans
              (congrArg (fun t => smSize + t)
                (Nat.sub_add_cancel (hiSize + hiSize) r
                  (Nat.le_trans hr_le (Nat.le_add_right hiSize hiSize))))
              (Eq.symm
                (Nat.sub_add_cancel (smSize + (hiSize + hiSize)) r
                  (Nat.le_trans hr_le
                    (Nat.le_trans (Nat.le_add_right hiSize hiSize)
                      (Nat.le_add_left' (hiSize + hiSize) smSize))))))))))
    (Nat.sub_le_sub_left hr_pos (smSize + (hiSize + hiSize)))

-- Theorem 3 Regime 1: M <= L0 * L0 + 2 * L0 and Q = L0 + 1 => M < Q * Q and c <= M / L.
theorem sq_succ_expand (L0 : Nat) :
    (L0 + 1) * (L0 + 1) = (L0 * L0 + (L0 + L0)) + 1 :=
  Eq.trans (Nat.right_distrib L0 1 (L0 + 1))
    (Eq.trans
      (Nat.add_congr
        (Eq.trans (Nat.left_distrib L0 L0 1)
          (congrArg (fun t => L0 * L0 + t) (Nat.mul_one L0)))
        (Nat.one_mul (L0 + 1)))
      (Eq.trans
        (Eq.symm (Nat.add_assoc (L0 * L0 + L0) L0 1))
        (congrArg (fun t => t + 1) (Nat.add_assoc (L0 * L0) L0 L0))))

theorem theorem3_regime1_q_sq_gt_m {M L0 : Nat}
    (hM : M ≤ L0 * L0 + (L0 + L0)) :
    M < (L0 + 1) * (L0 + 1) :=
  Nat.le_congr rfl (Eq.symm (sq_succ_expand L0)) (Nat.succ_le_succ hM)

theorem theorem3_regime1_cofactor {M L L0 q c : Nat}
    (hL_pos : 0 < L)
    (hL : L ≤ L0)
    (hq : L0 + 1 ≤ q)
    (hqc : q * c ≤ M) :
    c ≤ M / L :=
  div_ge_of_mul_le hL_pos
    (Nat.le_trans
      (Nat.mul_le_mul_right
        (Nat.le_trans (Nat.le_trans hL (Nat.le_succ L0)) hq)
        c)
      hqc)

-- Theorem 3 Regime 2: L <= L0 <= k and k * k <= M and c <= k => c <= M / L.
theorem theorem3_regime2_cofactor {M L L0 k c : Nat}
    (hL_pos : 0 < L)
    (hL : L ≤ L0)
    (hk : L0 ≤ k)
    (hk2 : k * k ≤ M)
    (hc : c ≤ k) :
    c ≤ M / L :=
  div_ge_of_mul_le hL_pos
    (Nat.le_trans
      (Nat.mul_le_mul (Nat.le_trans hL hk) hc)
      hk2)

end Erdos708Theorem3
