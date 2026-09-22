import RectangleColoring.LowerBound
import RectangleColoring.SmallCases

/-!
The complete minimum-height theorem, including rectangles of every orientation.
The only hypotheses are that `n` is a positive natural number and that the grid
uses the standard integer coordinates specified in `Basic.lean`.
-/

namespace RectangleColoring

/-- The threshold minus one does not force a monochromatic rectangle. -/
theorem lower_bound (n : ℕ) (hn : 0 < n) :
    ¬ ForcesRectangle n (n * blockSize n) := by
  rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with rfl | rfl | hn3
  · simpa [blockSize] using oneColor_lower
  · simpa [blockSize] using twoColor_lower
  · exact fun h => construction_avoids hn3 (h (construction n))

/-- Both forcing at the threshold and a counterexample at every smaller height. -/
theorem minimum_threshold (n : ℕ) (hn : 0 < n) :
    IsMinimum n (threshold n) := by
  refine ⟨upper_bound n, ?_⟩
  intro l hl
  apply not_forcesRectangle_of_le (L := n * blockSize n) ?_ (lower_bound n hn)
  unfold threshold at hl
  omega

theorem threshold_closed_form (n : ℕ) :
    threshold n = n ^ 2 * (n + 1) / 2 + 1 := by
  have h2 : (2 : ℤ) * ((n : ℤ) * (blockSize n : ℤ)) =
      (n : ℤ) * (n : ℤ) * ((n : ℤ) + 1) := by
    calc
      _ = (n : ℤ) * (2 * (blockSize n : ℤ)) := by ring
      _ = _ := by rw [twice_blockSize_int]; ring
  have h2' : 2 * (n * blockSize n) = n * n * (n + 1) := by exact_mod_cast h2
  simp only [threshold, pow_two]
  omega

/-- Answer to the original problem on the unit square lattice. -/
theorem minimum_height (n : ℕ) (hn : 0 < n) :
    IsMinimum n (n ^ 2 * (n + 1) / 2 + 1) := by
  rw [← threshold_closed_form]
  exact minimum_threshold n hn

#print axioms minimum_height

end RectangleColoring
