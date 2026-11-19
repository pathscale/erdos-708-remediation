-- Prop8.lean: DualKernel-verified formalization of Proposition 8's discrete hinge-integral
-- identity, scaled-interval cardinality dichotomy |I_{j,r}| in {floor(M/p_j^r), floor(M/p_j^r)+1},
-- two-step telescoping, and Proposition 8(1)'s smooth combinatorial matching step.

import Init
import Std
import NumberTheory

namespace Erdos708Prop8

def minNat (a b : Nat) : Nat := cond (Nat.ble a b) a b

theorem sub_zero_right (n : Nat) : n - 0 = n := rfl

theorem add_sub_cancel_right (a b : Nat) : (a + b) - b = a :=
  Nat.add_right_cancel (Nat.sub_add_cancel (a + b) b (Nat.le_add_left' b a))

theorem add_sub_cancel_left (a b : Nat) : (a + b) - a = b :=
  Eq.trans (congrArg (fun t => t - a) (Nat.add_comm a b)) (add_sub_cancel_right b a)

theorem sub_sub_sum_aux {u a b : Nat} (hab : a ≤ b) (hbu : b ≤ u) :
    ((b - a) + (u - b)) + a = (u - a) + a :=
  Eq.trans (Nat.add_right_comm (b - a) (u - b) a)
    (Eq.trans (congrArg (fun t => t + (u - b)) (Nat.sub_add_cancel b a hab))
      (Eq.trans (Nat.add_comm b (u - b))
        (Eq.trans (Nat.sub_add_cancel u b hbu)
          (Eq.symm (Nat.sub_add_cancel u a (Nat.le_trans hab hbu))))))

theorem sub_sub_cancel_chain {u a b : Nat} (hab : a ≤ b) (hbu : b ≤ u) :
    (u - a) - (u - b) = b - a :=
  Nat.add_right_cancel
    (Eq.trans (Nat.sub_add_cancel (u - a) (u - b) (Nat.sub_le_sub_left hab u))
      (Eq.symm (Nat.add_right_cancel (sub_sub_sum_aux hab hbu))))

-- Exact discrete counterpart of (u - a)_+ - (u - b)_+ = \int_a^b 1_{u > t} dt = (min(u, b) - a)_+
theorem hinge_step_identity (u a b : Nat) (hab : a ≤ b) :
    (u - a) - (u - b) = minNat u b - a :=
  @Bool.casesOn (fun c => Nat.ble u b = c → (u - a) - (u - b) = cond c u b - a) (Nat.ble u b)
    (fun h_false =>
      sub_sub_cancel_chain hab (Nat.le_trans (Nat.le_succ b) (Nat.lt_of_ble_eq_false h_false)))
    (fun h_true =>
      congrArg (fun t => (u - a) - t) (Nat.sub_eq_zero_of_le (Nat.le_of_ble_eq_true h_true)))
    rfl

theorem sub_mono_left {x y : Nat} (h : x ≤ y) (c : Nat) : x - c ≤ y - c :=
  @Bool.casesOn (fun b => Nat.ble c x = b → x - c ≤ y - c) (Nat.ble c x)
    (fun hf =>
      Nat.le_congr
        (Eq.symm (Nat.sub_eq_zero_of_le (Nat.le_trans (Nat.le_succ x) (Nat.lt_of_ble_eq_false hf))))
        rfl
        (Nat.zero_le (y - c)))
    (fun ht =>
      Nat.le_of_add_le_add_right c
        (Nat.le_congr
          (Eq.symm (Nat.sub_add_cancel x c (Nat.le_of_ble_eq_true ht)))
          (Eq.symm (Nat.sub_add_cancel y c (Nat.le_trans (Nat.le_of_ble_eq_true ht) h)))
          h))
    rfl

-- Two-step telescoping: (u2 - c) - (u0 - c) = ((u2 - c) - (u1 - c)) + ((u1 - c) - (u0 - c))
theorem hinge_two_step_telescope {u0 u1 u2 c : Nat} (h01 : u0 ≤ u1) (h12 : u1 ≤ u2) :
    (u2 - c) - (u0 - c) = ((u2 - c) - (u1 - c)) + ((u1 - c) - (u0 - c)) :=
  Eq.symm
    (Nat.add_right_cancel
      (Eq.trans (Nat.add_assoc ((u2 - c) - (u1 - c)) ((u1 - c) - (u0 - c)) (u0 - c))
        (Eq.trans
          (congrArg (fun t => ((u2 - c) - (u1 - c)) + t)
            (Nat.sub_add_cancel (u1 - c) (u0 - c) (sub_mono_left h01 c)))
          (Eq.trans (Nat.sub_add_cancel (u2 - c) (u1 - c) (sub_mono_left h12 c))
            (Eq.symm
              (Nat.sub_add_cancel (u2 - c) (u0 - c)
                (Nat.le_trans (sub_mono_left h01 c) (sub_mono_left h12 c))))))))

theorem divmod_sum_rearrange (q rx qx rM qM : Nat) :
    (rx + q * qx) + (rM + q * qM) = (rx + rM) + q * (qx + qM) :=
  Eq.trans (Nat.add_add_add_comm rx (q * qx) rM (q * qM))
    (congrArg (fun t => (rx + rM) + t) (Eq.symm (Nat.left_distrib q qx qM)))

theorem sum_sub_lt_of_lt {rx rM q : Nat} (hx : rx < q) (hM : rM < q) (hge : q ≤ rx + rM) :
    (rx + rM) - q < q :=
  Nat.le_of_add_le_add_right q
    (Nat.le_congr
      (Eq.symm
        (Eq.trans (Nat.add_right_comm ((rx + rM) - q) 1 q)
          (congrArg (fun t => t + 1) (Nat.sub_add_cancel (rx + rM) q hge))))
      rfl
      (Nat.le_trans
        (Nat.le_succ ((rx + rM) + 1))
        (Nat.le_congr
          (Eq.trans (Nat.add_add_add_comm rx 1 rM 1) rfl)
          rfl
          (Nat.add_le_add hx hM))))

theorem divmod_carry_rearrange (q s qs : Nat) (hge : q ≤ s) :
    s + q * qs = (s - q) + q * (qs + 1) :=
  Eq.trans (congrArg (fun t => t + q * qs) (Eq.symm (Nat.sub_add_cancel s q hge)))
    (Eq.trans (Nat.add_assoc (s - q) q (q * qs))
      (congrArg (fun t => (s - q) + t)
        (Eq.trans (Nat.add_comm q (q * qs)) (Eq.symm (Nat.mul_succ q qs)))))

-- Exact Scaled-Interval Cardinality Dichotomy (Proposition 8(2), line 163):
-- For every x, M, and prime power q > 0, (x + M) / q is either x / q + M / q or (x / q + M / q) + 1.
theorem scaled_interval_div_dichotomy (x M : Nat) {q : Nat} (hq : 0 < q) :
    Or ((x + M) / q = x / q + M / q) ((x + M) / q = (x / q + M / q) + 1) :=
  Or.elim (Nat.lt_or_ge (x % q + M % q) q)
    (fun hlt =>
      Or.inl
        (Nat.div_eq_of_eq hlt
          (Eq.trans
            (Nat.add_congr (Eq.symm (Nat.mod_add_div x q)) (Eq.symm (Nat.mod_add_div M q)))
            (divmod_sum_rearrange q (x % q) (x / q) (M % q) (M / q)))))
    (fun hge =>
      Or.inr
        (Nat.div_eq_of_eq
          (sum_sub_lt_of_lt (Nat.mod_lt x hq) (Nat.mod_lt M hq) hge)
          (Eq.trans
            (Nat.add_congr (Eq.symm (Nat.mod_add_div x q)) (Eq.symm (Nat.mod_add_div M q)))
            (Eq.trans (divmod_sum_rearrange q (x % q) (x / q) (M % q) (M / q))
              (divmod_carry_rearrange q (x % q + M % q) (x / q + M / q) hge)))))

-- Corollary: |I_{j,r}| = (x + M) / q - x / q >= M / q
theorem scaled_interval_card_ge_floor (x M : Nat) {q : Nat} (hq : 0 < q) :
    M / q ≤ (x + M) / q - x / q :=
  Or.elim (scaled_interval_div_dichotomy x M hq)
    (fun h0 =>
      Nat.le_of_eq
        (Eq.symm
          (Eq.trans (congrArg (fun t => t - x / q) h0) (add_sub_cancel_left (x / q) (M / q)))))
    (fun h1 =>
      Nat.le_congr rfl
        (Eq.symm
          (Eq.trans (congrArg (fun t => t - x / q) h1)
            (Eq.trans (congrArg (fun t => t - x / q) (Nat.add_assoc (x / q) (M / q) 1))
              (add_sub_cancel_left (x / q) (M / q + 1)))))
        (Nat.le_succ (M / q)))

-- Corollary: |I_{j,r}| = (x + M) / q - x / q <= M / q + 1
theorem scaled_interval_card_le_floor_succ (x M : Nat) {q : Nat} (hq : 0 < q) :
    (x + M) / q - x / q ≤ M / q + 1 :=
  Or.elim (scaled_interval_div_dichotomy x M hq)
    (fun h0 =>
      Nat.le_congr
        (Eq.symm
          (Eq.trans (congrArg (fun t => t - x / q) h0) (add_sub_cancel_left (x / q) (M / q))))
        rfl
        (Nat.le_succ (M / q)))
    (fun h1 =>
      Nat.le_of_eq
        (Eq.trans (congrArg (fun t => t - x / q) h1)
          (Eq.trans (congrArg (fun t => t - x / q) (Nat.add_assoc (x / q) (M / q) 1))
            (add_sub_cancel_left (x / q) (M / q + 1)))))

-- Proposition 8(1) Smooth Combinatorial Matching Dominance Step (scaled by denominator D):
-- If wp <= D and Xm <= Xpi + wp (since (sm_Q(m) / p) | pi(m)), then
-- (Xm - 2*D)_+ <= (Xpi - D)_+.
theorem smooth_matching_hinge_step {Xm Xpi wp D : Nat}
    (hwp : wp ≤ D) (hcov : Xm ≤ Xpi + wp) :
    Xm - (D + D) ≤ Xpi - D :=
  @Bool.casesOn (fun b => Nat.ble (D + D) Xm = b → Xm - (D + D) ≤ Xpi - D) (Nat.ble (D + D) Xm)
    (fun hf =>
      Nat.le_congr
        (Eq.symm (Nat.sub_eq_zero_of_le (Nat.le_trans (Nat.le_succ Xm) (Nat.lt_of_ble_eq_false hf))))
        rfl
        (Nat.zero_le (Xpi - D)))
    (fun ht =>
      Nat.le_of_add_le_add_right (D + D)
        (Nat.le_congr
          (Eq.symm (Nat.sub_add_cancel Xm (D + D) (Nat.le_of_ble_eq_true ht)))
          (Eq.symm
            (Eq.trans (Eq.symm (Nat.add_assoc (Xpi - D) D D))
              (congrArg (fun t => t + D)
                (Nat.sub_add_cancel Xpi D
                  (Nat.le_of_add_le_add_right D
                    (Nat.le_trans (Nat.le_of_ble_eq_true ht)
                      (Nat.le_trans hcov (Nat.add_le_add_left hwp Xpi))))))))
          (Nat.le_trans hcov (Nat.add_le_add_left hwp Xpi))))
    rfl

end Erdos708Prop8
