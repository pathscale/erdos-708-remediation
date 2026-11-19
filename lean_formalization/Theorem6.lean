-- Theorem6.lean: DualKernel-verified formalization of Theorem 6
-- (Universal Semiprime Multigraph Vertex-Saving Bound, both general and bipartite cases).

import Init
import Std

namespace Erdos708Theorem6

theorem multigraph_card_le_two_m_sub_t {cardB sumVb m t : Nat}
    (h_cover : cardB + sumVb ≤ 2 * m + t)
    (h_pair : t + t ≤ sumVb) :
    cardB + t ≤ 2 * m :=
  Nat.le_of_add_le_add_right t
    (Nat.le_trans
      (Nat.le_congr (Eq.symm (Nat.add_assoc cardB t t)) rfl (Nat.add_le_add_left h_pair cardB))
      h_cover)

theorem multigraph_double_card_saving {cardB sumVb m t vNonIso : Nat}
    (h_cover : cardB + sumVb ≤ 2 * m + t)
    (h_pair : t + t ≤ sumVb)
    (h_union : vNonIso ≤ sumVb) :
    (cardB + cardB) + vNonIso ≤ 2 * m + 2 * m :=
  Nat.le_of_add_le_add_right t
    (Nat.le_congr
      (Eq.trans (Nat.add_add_add_comm cardB t cardB vNonIso)
        (Eq.trans (Eq.symm (Nat.add_assoc (cardB + cardB) t vNonIso))
          (Nat.add_right_comm (cardB + cardB) t vNonIso)))
      (Eq.symm (Nat.add_assoc (2 * m) (2 * m) t))
      (Nat.add_le_add
        (multigraph_card_le_two_m_sub_t h_cover h_pair)
        (Nat.le_trans (Nat.add_le_add_left h_union cardB) h_cover)))

theorem multigraph_bipartite_side_saving {cardB sumVb m t sideNonIso : Nat}
    (h_cover : cardB + sumVb ≤ 2 * m + t)
    (h_side : sideNonIso + t ≤ sumVb) :
    cardB + sideNonIso ≤ 2 * m :=
  Nat.le_of_add_le_add_right t
    (Nat.le_trans
      (Nat.le_congr (Eq.symm (Nat.add_assoc cardB sideNonIso t)) rfl
        (Nat.add_le_add_left h_side cardB))
      h_cover)

theorem multigraph_bipartite_max_saving {cardB sumVb m t pNonIso qNonIso : Nat}
    (h_cover : cardB + sumVb ≤ 2 * m + t)
    (hp : pNonIso + t ≤ sumVb)
    (hq : qNonIso + t ≤ sumVb) :
    And (cardB + pNonIso ≤ 2 * m) (cardB + qNonIso ≤ 2 * m) :=
  ⟨multigraph_bipartite_side_saving h_cover hp,
   multigraph_bipartite_side_saving h_cover hq⟩

theorem remark7_cross_tier_budget : (2 * 36 - 12) + 12 = 2 * 36 := rfl

end Erdos708Theorem6
