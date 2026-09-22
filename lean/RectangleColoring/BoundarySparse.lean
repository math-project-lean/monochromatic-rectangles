import RectangleColoring.BoundaryStructure
import RectangleColoring.BoundaryArithmetic

/-! Special-point slope estimates across a normal block boundary. -/

namespace RectangleColoring.BoundarySparse

open BoundaryStructure BoundaryArithmetic

private theorem special_bounds {n k M x y : ℤ} (hk : 1 ≤ k)
    (h : BoundarySpecial n k M x y) : 1 ≤ x ∧ x ≤ n := by
  rcases h with h | h <;> omega

private theorem same_column_order {a b K ya yb : ℤ}
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hya : 2 * ya = a * (a - 1) + K)
    (hyb : 2 * yb = b * (b - 1) + K)
    (hy : ya < yb) : a < b := by
  by_contra h
  have hprod : 0 ≤ (a - b) * (a + b - 1) :=
    mul_nonneg (by omega) (by omega)
  nlinarith

/-- Every new-block special point lies above every old-block special point. -/
private theorem old_before_new {n k M a b ya yb : ℤ}
    (hn : 3 ≤ n) (ha : 1 ≤ a) (hb : 1 ≤ b) (hbn : b ≤ n)
    (hM : 2 * M = n * (n + 1))
    (hold : 2 * yb = b * (b - 1) + 2 * k)
    (hnew : 2 * ya = 2 * M + a * (a - 1) + 2 * (k - 1)) :
    yb < ya := by
  have hprod : 0 ≤ (n - b) * (n + b - 1) :=
    mul_nonneg (by omega) (by omega)
  have htri : 0 ≤ a * (a - 1) := mul_nonneg (by omega) (by omega)
  nlinarith

/-- An upward pair is either an increasing pair in one block, or an old/new pair. -/
private theorem pair_cases {n k M xa ya xb yb : ℤ}
    (hn : 3 ≤ n) (hk : 1 ≤ k) (hM : 2 * M = n * (n + 1))
    (ha : BoundarySpecial n k M xa ya) (hb : BoundarySpecial n k M xb yb)
    (hy : ya < yb) :
    (xa < xb ∧ 2 * (yb - ya) = xb * (xb - 1) - xa * (xa - 1)) ∨
      2 * (yb - ya) = 2 * M + xb * (xb - 1) - xa * (xa - 1) - 2 := by
  rcases ha with ⟨hka, han, hea⟩ | ⟨hka, han, hea⟩ <;>
    rcases hb with ⟨hkb, hbn, heb⟩ | ⟨hkb, hbn, heb⟩
  · left
    exact ⟨same_column_order (by omega) (by omega) hea heb hy,
      same_block_difference hea heb⟩
  · right
    exact cross_difference hea heb
  · have hrev := old_before_new hn (by omega : 1 ≤ xa)
      (by omega : 1 ≤ xb) hbn hM heb hea
    omega
  · left
    have hea' : 2 * ya = xa * (xa - 1) + (2 * M + 2 * (k - 1)) := by omega
    have heb' : 2 * yb = xb * (xb - 1) + (2 * M + 2 * (k - 1)) := by omega
    exact ⟨same_column_order (by omega) (by omega) hea' heb' hy,
      same_block_difference hea' heb'⟩

theorem sparse_pos {n k M xa ya xb yb : ℤ}
    (hn : 3 ≤ n) (hk : 1 ≤ k) (hM : 2 * M = n * (n + 1))
    (ha : BoundarySpecial n k M xa ya) (hb : BoundarySpecial n k M xb yb)
    (hx : xa < xb) (hy : ya < yb) : xb - xa ≤ yb - ya := by
  have hxa := (special_bounds hk ha).1
  rcases pair_cases hn hk hM ha hb hy with ⟨_, he⟩ | he
  · exact same_block_slope_bound hxa hx he
  · have := cross_ascending_bound hn hxa hx hM he
    omega

theorem sparse_pos_eq {n k M xa ya xb yb : ℤ}
    (hn : 3 ≤ n) (hk : 1 ≤ k) (hM : 2 * M = n * (n + 1))
    (ha : BoundarySpecial n k M xa ya) (hb : BoundarySpecial n k M xb yb)
    (hx : xa < xb) (hy : ya < yb) (heq : xb - xa = yb - ya) :
    xa = 1 ∧ xb = 2 := by
  have hxa := (special_bounds hk ha).1
  rcases pair_cases hn hk hM ha hb hy with ⟨_, he⟩ | he
  · exact same_block_slope_eq hxa hx he heq.symm
  · have := cross_ascending_bound hn hxa hx hM he
    omega

theorem sparse_neg {n k M xa ya xb yb : ℤ}
    (hn : 3 ≤ n) (hk : 1 ≤ k) (hM : 2 * M = n * (n + 1))
    (ha : BoundarySpecial n k M xa ya) (hb : BoundarySpecial n k M xb yb)
    (hx : xb < xa) (hy : ya < yb) : xa - xb ≤ yb - ya := by
  have hxb := (special_bounds hk hb).1
  have hxan := (special_bounds hk ha).2
  rcases pair_cases hn hk hM ha hb hy with ⟨hinc, _⟩ | he
  · omega
  · exact cross_descending_bound hxb hx hxan hM he

theorem sparse_neg_eq {n k M xa ya xb yb : ℤ}
    (hn : 3 ≤ n) (hk : 1 ≤ k) (hM : 2 * M = n * (n + 1))
    (ha : BoundarySpecial n k M xa ya) (hb : BoundarySpecial n k M xb yb)
    (hx : xb < xa) (hy : ya < yb) (heq : xa - xb = yb - ya) :
    xa = n ∧ xb = 1 := by
  have hxb := (special_bounds hk hb).1
  have hxan := (special_bounds hk ha).2
  rcases pair_cases hn hk hM ha hb hy with ⟨hinc, _⟩ | he
  · omega
  · obtain ⟨hb1, han⟩ := cross_descending_eq hxb hx hxan hM he heq.symm
    exact ⟨han, hb1⟩

theorem sparse_neg_gap {n k M xa ya xb yb : ℤ}
    (hn : 3 ≤ n) (hk : 1 ≤ k) (hM : 2 * M = n * (n + 1))
    (ha : BoundarySpecial n k M xa ya) (hb : BoundarySpecial n k M xb yb)
    (hx : xa = xb + 1) (hy : ya < yb) : M - n ≤ yb - ya := by
  have hxan := (special_bounds hk ha).2
  rcases pair_cases hn hk hM ha hb hy with ⟨hinc, _⟩ | he
  · omega
  · exact (cross_adjacent_columns hx hxan he).2

end RectangleColoring.BoundarySparse
