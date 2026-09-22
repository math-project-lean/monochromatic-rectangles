import RectangleColoring.LocalAvoidance

/-! Integer row/block bookkeeping and height bounds for the global argument. -/

namespace RectangleColoring.BlockArithmetic

/-- Ordering two rows also orders their block indices. -/
theorem block_index_mono {M sa sp ua up ya yp : ℤ}
    (hM : 0 < M) (hua : 0 ≤ ua) (_hua' : ua < M)
    (_hup : 0 ≤ up) (hup' : up < M)
    (hya : ya = sa * M + ua) (hyp : yp = sp * M + up)
    (hy : ya ≤ yp) : sa ≤ sp := by
  by_contra h
  have hd : 0 ≤ (sa - sp - 1) * M := mul_nonneg (by omega) (by omega)
  nlinarith

/-- Rows separated by less than one block belong either to the same block
or to successive blocks. -/
theorem block_index_same_or_next {M sa sp ua up ya yp : ℤ}
    (hM : 0 < M) (hua : 0 ≤ ua) (hua' : ua < M)
    (hup : 0 ≤ up) (hup' : up < M)
    (hya : ya = sa * M + ua) (hyp : yp = sp * M + up)
    (hy : ya ≤ yp) (hd : yp - ya < M) : sp = sa ∨ sp = sa + 1 := by
  have hs := block_index_mono hM hua hua' hup hup' hya hyp hy
  have hsp : sp ≤ sa + 1 := by
    by_contra h
    have hm : 0 ≤ (sp - sa - 2) * M := mul_nonneg (by omega) (by omega)
    nlinarith
  omega

/-- Integer version of the height bound used at a cyclic block boundary. -/
theorem height_le_triangular_int {n : ℤ} (hn : 3 ≤ n) :
    n * n / 4 + 1 ≤ n * (n - 1) / 2 := by
  by_cases h3 : n = 3
  · subst n
    norm_num
  · have hn4 : 4 ≤ n := by omega
    have hdiv : 4 * (n * n / 4) ≤ n * n := by omega
    have hsquare : 4 * n ≤ n * n := by
      nlinarith [mul_nonneg (show 0 ≤ n by omega) (show 0 ≤ n - 4 by omega)]
    have hb : 2 * (n * n / 4 + 1) ≤ n * (n - 1) := by nlinarith
    omega

/-- In block-size notation, the same upper bound reads H ≤ M - n. -/
theorem height_le_block_sub_n {n M : ℤ} (hn : 3 ≤ n)
    (hM : 2 * M = n * (n + 1)) : n * n / 4 + 1 ≤ M - n := by
  have hh := height_le_triangular_int hn
  have heq : n * (n - 1) = 2 * (M - n) := by nlinarith
  omega

theorem height_lt_block_sub_n_add_one {n M : ℤ} (hn : 3 ≤ n)
    (hM : 2 * M = n * (n + 1)) : n * n / 4 + 1 < M - n + 1 := by
  have := height_le_block_sub_n hn hM
  omega

theorem height_lt_block_int {n M : ℤ} (hn : 3 ≤ n)
    (hM : 2 * M = n * (n + 1)) : n * n / 4 + 1 < M := by
  have := height_le_block_sub_n hn hM
  omega

/-- Before the last triangular transition, color n-1 occurs only in the
rightmost column. This is the cyclic-boundary exclusion. -/
theorem wrap_blockColor_at_right_edge {n x v : ℤ}
    (hx : x ≤ n) (hv : 2 * v < n * (n - 1))
    (hc : LocalAvoidance.BlockColor (n - 1) x v) : x = n := by
  rcases hc with ho | hs
  · rcases ho with ⟨hx', hv'⟩ | ⟨hx', hv'⟩
    · omega
    · nlinarith
  · rcases hs with ⟨hx', hv'⟩
    omega

end RectangleColoring.BlockArithmetic
