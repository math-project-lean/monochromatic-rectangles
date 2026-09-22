import Mathlib.Tactic

/-!
Elementary arithmetic geometry used by the proposed lower-bound construction.
These lemmas do not by themselves assert that the construction has no rectangles.
-/

namespace RectangleColoring.Geometry

/-- For positive integral vertical increments, their sum is at most their
product plus one. This is `(q - 1) * (t - 1) ≥ 0`. -/
theorem positive_sum_le_product_add_one {q t : ℕ}
    (hq : 0 < q) (ht : 0 < t) : q + t ≤ q * t + 1 := by
  obtain ⟨q', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  obtain ⟨t', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  nlinarith

/-- A product of two nonnegative widths with sum at most `n` is at most
`⌊n² / 4⌋`. -/
theorem product_le_quarter_square {p r n : ℕ} (hw : p + r ≤ n) :
    p * r ≤ n * n / 4 := by
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 4)).2
  have hs : (p + r) * (p + r) ≤ n * n := Nat.mul_self_le_mul_self hw
  nlinarith [sq_nonneg ((p : ℤ) - (r : ℤ))]

/-- The vertical span of a tilted integer rectangle of horizontal span at
most `n` is at most `⌊n² / 4⌋ + 1`. The orthogonality equation is `q*t=p*r`. -/
theorem tilted_height_bound {p q r t n : ℕ}
    (hq : 0 < q) (ht : 0 < t)
    (hperp : q * t = p * r) (hw : p + r ≤ n) :
    q + t ≤ n * n / 4 + 1 := by
  calc
    q + t ≤ q * t + 1 := positive_sum_le_product_add_one hq ht
    _ = p * r + 1 := by rw [hperp]
    _ ≤ n * n / 4 + 1 := Nat.add_le_add_right (product_le_quarter_square hw) 1

/-- The same height estimate stated directly for integer coordinates. -/
theorem tilted_height_bound_int {p q r t n : ℤ}
    (hp : 0 ≤ p) (hq : 0 < q) (hr : 0 ≤ r) (ht : 0 < t)
    (hperp : q * t = p * r) (hw : p + r ≤ n) :
    q + t ≤ n * n / 4 + 1 := by
  have hqt : 0 ≤ (q - 1) * (t - 1) := mul_nonneg (by omega) (by omega)
  have hw' : 0 ≤ (n - p - r) * (n + p + r) :=
    mul_nonneg (by omega) (by omega)
  have hbound : 4 * (q + t - 1) ≤ n * n := by
    nlinarith [sq_nonneg (p - r)]
  omega

/-- For at least three colors the possible tilted height fits inside the
first `n*(n-1)/2` rows of a block. -/
theorem height_le_triangular {n : ℕ} (hn : 3 ≤ n) :
    n * n / 4 + 1 ≤ n * (n - 1) / 2 := by
  by_cases h3 : n = 3
  · subst n
    norm_num
  · have hn4 : 4 ≤ n := by omega
    have hsub : n - 1 + 1 = n := by omega
    have hdiv : 4 * (n * n / 4) ≤ n * n := by omega
    have hsquare : 4 * n ≤ n * n := by
      nlinarith [Nat.mul_le_mul_left n hn4]
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
    nlinarith

/-- In particular, a tilted rectangle is shorter than one block. -/
theorem height_lt_block {n : ℕ} (hn : 3 ≤ n) :
    n * n / 4 + 1 < n * (n + 1) / 2 := by
  have h := height_le_triangular hn
  have hsub : n - 1 + 1 = n := by omega
  have heq : n * (n + 1) = n * (n - 1) + 2 * n := by nlinarith
  omega

/-- A monotone chain has no right angle at its middle point. Coordinates
are integral so this is an exact dot-product assertion. -/
theorem monotone_middle_dot_negative
    {ax ay bx by_ cx cy : ℤ}
    (hx₁ : ax ≤ bx) (hx₂ : bx ≤ cx)
    (hy₁ : ay < by_) (hy₂ : by_ < cy) :
    (ax - bx) * (cx - bx) + (ay - by_) * (cy - by_) < 0 := by
  have h₁ : (ax - bx) * (cx - bx) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega)
  have h₂ : (ay - by_) * (cy - by_) < 0 :=
    mul_neg_of_neg_of_pos (by omega) (by omega)
  omega

/-- A monotone chain has no right angle at its first point. -/
theorem monotone_first_dot_positive
    {ax ay bx by_ cx cy : ℤ}
    (hx₁ : ax ≤ bx) (hx₂ : bx ≤ cx)
    (hy₁ : ay < by_) (hy₂ : by_ < cy) :
    (bx - ax) * (cx - ax) + (by_ - ay) * (cy - ay) > 0 := by
  have h₁ : 0 ≤ (bx - ax) * (cx - ax) :=
    mul_nonneg (by omega) (by omega)
  have h₂ : 0 < (by_ - ay) * (cy - ay) :=
    mul_pos (by omega) (by omega)
  omega

/-- A monotone chain has no right angle at its last point. -/
theorem monotone_last_dot_positive
    {ax ay bx by_ cx cy : ℤ}
    (hx₁ : ax ≤ bx) (hx₂ : bx ≤ cx)
    (hy₁ : ay < by_) (hy₂ : by_ < cy) :
    (ax - cx) * (bx - cx) + (ay - cy) * (by_ - cy) > 0 := by
  have h₁ : 0 ≤ (ax - cx) * (bx - cx) :=
    mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  have h₂ : 0 < (ay - cy) * (by_ - cy) :=
    mul_pos_of_neg_of_neg (by omega) (by omega)
  omega

end RectangleColoring.Geometry
