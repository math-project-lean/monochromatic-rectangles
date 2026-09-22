import Mathlib.Tactic

/-!
Exact integer slope arithmetic for the special points in two adjacent blocks.
All triangular-coordinate equations are doubled, avoiding division and casts.
-/

namespace RectangleColoring.BoundaryArithmetic

/-- The vertical difference between old- and new-block special points. -/
theorem cross_difference {M k a b yOld yNew : ℤ}
    (hOld : 2 * yOld = b * (b - 1) + 2 * k)
    (hNew : 2 * yNew = 2 * M + a * (a - 1) + 2 * (k - 1)) :
    2 * (yNew - yOld) = 2 * M + a * (a - 1) - b * (b - 1) - 2 := by
  omega

/-- A cross-block segment pointing left has slope of absolute value at least one. -/
theorem cross_descending_bound {n M a b D : ℤ}
    (ha : 1 ≤ a) (hab : a < b) (hbn : b ≤ n)
    (hM : 2 * M = n * (n + 1))
    (hD : 2 * D = 2 * M + a * (a - 1) - b * (b - 1) - 2) :
    b - a ≤ D := by
  have h₁ : 0 ≤ (n - b) * (n + b + 1) :=
    mul_nonneg (by omega) (by omega)
  have h₂ : 0 ≤ (a - 1) * (a + 2) :=
    mul_nonneg (by omega) (by omega)
  nlinarith

/-- Equality in the descending slope estimate forces the extreme columns 1 and n. -/
theorem cross_descending_eq {n M a b D : ℤ}
    (ha : 1 ≤ a) (hab : a < b) (hbn : b ≤ n)
    (hM : 2 * M = n * (n + 1))
    (hD : 2 * D = 2 * M + a * (a - 1) - b * (b - 1) - 2)
    (heq : D = b - a) : a = 1 ∧ b = n := by
  have h₁ : 0 ≤ (n - b) * (n + b + 1) :=
    mul_nonneg (by omega) (by omega)
  have h₂ : 0 ≤ (a - 1) * (a + 2) :=
    mul_nonneg (by omega) (by omega)
  have hz₁ : (n - b) * (n + b + 1) = 0 := by nlinarith
  have hz₂ : (a - 1) * (a + 2) = 0 := by nlinarith
  have hn : n - b = 0 :=
    (mul_eq_zero.mp hz₁).resolve_right (by omega)
  have ha' : a - 1 = 0 :=
    (mul_eq_zero.mp hz₂).resolve_right (by omega)
  omega

/-- With the block's color index restored, the equality case also forces k = 1. -/
theorem cross_descending_eq_with_color {n M k a b D : ℤ}
    (hk : 1 ≤ k) (hka : k ≤ a) (hab : a < b) (hbn : b ≤ n)
    (hM : 2 * M = n * (n + 1))
    (hD : 2 * D = 2 * M + a * (a - 1) - b * (b - 1) - 2)
    (heq : D = b - a) : a = 1 ∧ b = n ∧ k = 1 := by
  obtain ⟨ha, hb⟩ := cross_descending_eq (by omega : 1 ≤ a) hab hbn hM hD heq
  omega

/-- A cross-block segment pointing right has slope strictly greater than one. -/
theorem cross_ascending_bound {n M a b D : ℤ}
    (hn : 3 ≤ n) (hb : 1 ≤ b) (hba : b < a)
    (hM : 2 * M = n * (n + 1))
    (hD : 2 * D = 2 * M + a * (a - 1) - b * (b - 1) - 2) :
    a - b < D := by
  have h₁ : 0 ≤ (a - b) * (a + b - 3) :=
    mul_nonneg (by omega) (by omega)
  nlinarith [sq_nonneg (n - 3)]

/-- Equal columns in adjacent blocks are separated by exactly M - 1 rows. -/
theorem cross_same_column {M a b D : ℤ}
    (hab : a = b)
    (hD : 2 * D = 2 * M + a * (a - 1) - b * (b - 1) - 2) :
    D = M - 1 := by
  subst b
  omega

/-- Adjacent descending columns give the large vertical separation M - 1 - a. -/
theorem cross_adjacent_columns {n M a b D : ℤ}
    (hab : b = a + 1) (hbn : b ≤ n)
    (hD : 2 * D = 2 * M + a * (a - 1) - b * (b - 1) - 2) :
    D = M - 1 - a ∧ M - n ≤ D := by
  subst b
  constructor <;> nlinarith

/-- The difference equation for two points on one translated triangular parabola. -/
theorem same_block_difference {K a b ya yb : ℤ}
    (ha : 2 * ya = a * (a - 1) + K)
    (hb : 2 * yb = b * (b - 1) + K) :
    2 * (yb - ya) = b * (b - 1) - a * (a - 1) := by
  omega

/-- The slope between distinct positive columns of one special-point parabola
is at least one. -/
theorem same_block_slope_bound {a b D : ℤ}
    (ha : 1 ≤ a) (hab : a < b)
    (hD : 2 * D = b * (b - 1) - a * (a - 1)) : b - a ≤ D := by
  have h : 0 ≤ (b - a) * (a + b - 3) :=
    mul_nonneg (by omega) (by omega)
  nlinarith

/-- Slope one in a single block occurs only at columns 1 and 2. -/
theorem same_block_slope_eq {a b D : ℤ}
    (ha : 1 ≤ a) (hab : a < b)
    (hD : 2 * D = b * (b - 1) - a * (a - 1))
    (heq : D = b - a) : a = 1 ∧ b = 2 := by
  have hz : (b - a) * (a + b - 3) = 0 := by nlinarith
  have hz' : a + b - 3 = 0 :=
    (mul_eq_zero.mp hz).resolve_left (by omega)
  omega

/-- Two perpendicular segments whose absolute slopes are at least one must
both have absolute slope exactly one. -/
theorem steep_perpendicular_unit {p q r t : ℤ}
    (hp : 0 < p) (hr : 0 < r) (hpq : p ≤ q) (hrt : r ≤ t)
    (hperp : q * t = p * r) : q = p ∧ t = r := by
  have hq : 0 < q := by omega
  have h₁ : p * r ≤ q * r := mul_le_mul_of_nonneg_right hpq (by omega)
  have h₂ : q * r ≤ q * t := mul_le_mul_of_nonneg_left hrt (by omega)
  have hz₁ : (q - p) * r = 0 := by nlinarith
  have hz₂ : q * (t - r) = 0 := by nlinarith
  have heq₁ : q - p = 0 := (mul_eq_zero.mp hz₁).resolve_right (by omega)
  have heq₂ : t - r = 0 := (mul_eq_zero.mp hz₂).resolve_left (by omega)
  omega

end RectangleColoring.BoundaryArithmetic
