import RectangleColoring.Classification
import RectangleColoring.Normalization
import RectangleColoring.Geometry
import RectangleColoring.BlockArithmetic
import RectangleColoring.BoundaryStructure
import RectangleColoring.BoundaryBlockAvoidance

namespace RectangleColoring

theorem construction_not_axis (n : ℕ) : ¬ AxisMono (construction n) := by
  rintro ⟨i, j, r, s, hij, hrs, h₁, h₂, h₃⟩
  have hs : construction n (i, s) = construction n (j, s) := h₃.symm.trans h₂
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hrs (construction_pair_unique i j hlt r s h₁ hs h₃)
  · exact hrs (construction_pair_unique j i hgt r s h₁.symm hs.symm
      (h₁.symm.trans h₂))

theorem xCoord_bounds {n l : ℕ} (p : Grid n l) :
    0 ≤ xCoord p ∧ xCoord p ≤ (n : ℤ) := by
  have := p.1.isLt
  simp only [xCoord]
  constructor
  · positivity
  · exact_mod_cast Nat.le_of_lt_succ p.1.isLt

/-- In a single block, equal colors have the same local geometric color class. -/
theorem point_same_block {n : ℕ} (a p : Grid n (n * blockSize n))
    (hc : construction n p = construction n a) (hb : blockOf p = blockOf a) :
    LocalAvoidance.BlockColor (((construction n a - blockOf a).val : ℕ) : ℤ)
      (xCoord p) (yCoord p - ((blockOf a).val : ℤ) * (blockSize n : ℤ)) := by
  have h := construction_point_blockColor p (construction n a) hc
  simpa only [localHeight, hb] using h

/-- Blocks are ordered in the same direction as global row coordinates. -/
theorem blockOf_mono {n : ℕ} (a p : Grid n (n * blockSize n))
    (hlo : yCoord a ≤ yCoord p) : (blockOf a).val ≤ (blockOf p).val := by
  have ha := localHeight_bounds a
  have hp := localHeight_bounds p
  have hm : 0 < (blockSize n : ℤ) := by omega
  dsimp only [localHeight] at ha hp
  by_contra hn
  have hd : 0 ≤ (((blockOf a).val : ℤ) - ((blockOf p).val : ℤ) - 1) *
      (blockSize n : ℤ) := mul_nonneg (by omega) (by omega)
  nlinarith

theorem next_block_localHeight {n : ℕ} (a p : Grid n (n * blockSize n))
    (hb : (blockOf p).val = (blockOf a).val + 1) :
    localHeight p = yCoord p - ((blockOf a).val : ℤ) * (blockSize n : ℤ) -
      (blockSize n : ℤ) := by
  have hb' : ((blockOf p).val : ℤ) = ((blockOf a).val : ℤ) + 1 := by
    exact_mod_cast hb
  simp only [localHeight, hb']
  ring

/-- Pointwise membership in the ordinary, non-wrapping pair of blocks. -/
theorem point_boundary_membership {n : ℕ} (a p : Grid n (n * blockSize n))
    (hc : construction n p = construction n a)
    (hlo : yCoord a ≤ yCoord p)
    (hhi : yCoord p - yCoord a < (blockSize n : ℤ))
    (hk : 0 < (construction n a - blockOf a).val) :
    let k : ℤ := (construction n a - blockOf a).val
    let M : ℤ := blockSize n
    let v : ℤ := yCoord p - ((blockOf a).val : ℤ) * M
    (0 ≤ v ∧ v < M ∧ LocalAvoidance.BlockColor k (xCoord p) v) ∨
    (M ≤ v ∧ v < 2 * M ∧ LocalAvoidance.BlockColor (k - 1) (xCoord p) (v - M)) := by
  dsimp only
  rcases blockOf_band a p hlo hhi with hb | hb
  · left
    have hbounds := localHeight_bounds p
    simp only [localHeight, hb] at hbounds
    exact ⟨hbounds.1, hbounds.2, point_same_block a p hc hb⟩
  · right
    have hbounds := localHeight_bounds p
    have hclass := construction_point_blockColor p (construction n a) hc
    have hshift := localColor_next_block_of_pos (construction n a)
      (blockOf a) (blockOf p) hb hk
    have hshift' : ((construction n a - blockOf p).val : ℤ) =
        ((construction n a - blockOf a).val : ℤ) - 1 := by omega
    rw [next_block_localHeight a p hb] at hbounds hclass
    rw [hshift'] at hclass
    exact ⟨by omega, by omega, hclass⟩

theorem twice_blockSize_int (n : ℕ) :
    2 * (blockSize n : ℤ) = (n : ℤ) * ((n : ℤ) + 1) := by
  have h := twice_choose_two_int (n + 1)
  change 2 * ((n + 1).choose 2 : ℤ) = _
  push_cast at h
  nlinarith

/-- The explicit construction avoids tilted rectangles for every `n ≥ 3`. -/
theorem construction_not_tilted {n : ℕ} (hn : 3 ≤ n) :
    ¬ TiltedMono (construction n) := by
  rintro ⟨a, b, c, d, x, y, p, q, r, t,
    hp, hq, hr, ht, hperp, hw, hxa, hya, hxb, hyb, hxc, hyc, hxd, hyd,
    hab, hac, had⟩
  let M : ℤ := blockSize n
  let H : ℤ := (n : ℤ) * (n : ℤ) / 4 + 1
  let s := blockOf a
  let col := construction n a
  let k₀ := (col - s).val
  let k : ℤ := k₀
  let z : ℤ := (s.val : ℤ) * M
  have hn' : (3 : ℤ) ≤ n := by exact_mod_cast hn
  have hM : 2 * M = (n : ℤ) * ((n : ℤ) + 1) := twice_blockSize_int n
  have hheight : q + t ≤ H :=
    Geometry.tilted_height_bound_int (by omega) hq (by omega) ht hperp hw
  have hHM : H < M := BlockArithmetic.height_lt_block_int hn' hM
  have hgap : H < M - (n : ℤ) + 1 :=
    BlockArithmetic.height_lt_block_sub_n_add_one hn' hM
  have hband (w : Grid n (n * blockSize n))
      (hlo : yCoord a ≤ yCoord w) (hhi : yCoord w ≤ yCoord c) :
      blockOf w = s ∨ (blockOf w).val = s.val + 1 := by
    apply blockOf_band a w hlo
    change yCoord w - yCoord a < M
    omega
  by_cases hk0 : k₀ = 0
  · by_cases hcs : blockOf c = s
    · have hs_all (w : Grid n (n * blockSize n))
          (hlo : yCoord a ≤ yCoord w) (hhi : yCoord w ≤ yCoord c) :
          blockOf w = s := by
        have h₁ := blockOf_mono a w hlo
        have h₂ := blockOf_mono w c hhi
        rw [hcs] at h₂
        exact Fin.ext (by omega)
      have hcb := point_same_block a b hab.symm (hs_all b (by omega) (by omega))
      have hcc := point_same_block a c hac.symm hcs
      have hcd := point_same_block a d had.symm (hs_all d (by omega) (by omega))
      change LocalAvoidance.BlockColor k (xCoord b) (yCoord b - z) at hcb
      change LocalAvoidance.BlockColor k (xCoord c) (yCoord c - z) at hcc
      change LocalAvoidance.BlockColor k (xCoord d) (yCoord d - z) at hcd
      rw [hxb, hyb, show y + q - z = (y - z) + q by ring] at hcb
      rw [hxc, hyc, show y + q + t - z = (y - z) + q + t by ring] at hcc
      rw [hxd, hyd, show y + t - z = (y - z) + t by ring] at hcd
      exact LocalAvoidance.blockColor_no_tilted (by dsimp [k]; positivity)
        hp hq hr ht hcb hcc hcd
    · have hnext := (hband c (by omega) (by omega)).resolve_left hcs
      have hshift := localColor_next_block_of_zero col s (blockOf c) hnext hk0
      have hshift' : ((col - blockOf c).val : ℤ) = (n : ℤ) - 1 := by
        have hn0 : 0 < n := by omega
        omega
      have hcc := construction_point_blockColor c col hac.symm
      rw [hshift'] at hcc
      have hlc : localHeight c = localHeight a + q + t - M := by
        have he := next_block_localHeight a c hnext
        rw [he]
        simp only [localHeight, hya, hyc]
        change y + q + t - (s.val : ℤ) * M - M =
          y - (s.val : ℤ) * M + q + t - M
        ring
      have haBound := localHeight_bounds a
      have haM : localHeight a < M := haBound.2
      have hcH : localHeight c < H := by omega
      have htri := BlockArithmetic.height_le_triangular_int hn'
      have hxcN : xCoord c = (n : ℤ) :=
        BlockArithmetic.wrap_blockColor_at_right_edge (xCoord_bounds c).2 (by
          change localHeight c < (n : ℤ) * (n : ℤ) / 4 + 1 at hcH
          omega) hcc
      have hbN := (xCoord_bounds b).2
      omega
  · have hk0pos : 0 < k₀ := by omega
    have hk : 1 ≤ k := by dsimp [k]; omega
    have hkn : k < (n : ℤ) := by
      have h := (col - s).isLt
      change ((col - s).val : ℤ) < (n : ℤ)
      exact_mod_cast h
    let A : ℤ := (k₀ + 1).choose 2
    have hA : 2 * A = k * (k + 1) := by
      have h := twice_choose_two_int (k₀ + 1)
      dsimp [A, k]
      push_cast at h
      nlinarith
    have hpoint (w : Grid n (n * blockSize n))
        (hcw : construction n w = col)
        (hlo : yCoord a ≤ yCoord w) (hhi : yCoord w ≤ yCoord c) :
        BoundaryStructure.BoundaryOrdinary k A M (xCoord w) (yCoord w - z) ∨
        BoundaryStructure.BoundarySpecial (n : ℤ) k M (xCoord w) (yCoord w - z) := by
      apply BoundaryStructure.blockColor_boundary_of_parameters
        hn' hk hkn hM hA (xCoord_bounds w).2
      exact point_boundary_membership a w hcw hlo (by
        change yCoord w - yCoord a < M
        omega) hk0pos
    have hB := hpoint a rfl (by omega) (by omega)
    have hR := hpoint b hab.symm (by omega) (by omega)
    have hT := hpoint c hac.symm (by omega) (by omega)
    have hL := hpoint d had.symm (by omega) (by omega)
    rw [hxa, hya] at hB
    rw [hxb, hyb, show y + q - z = (y - z) + q by ring] at hR
    rw [hxc, hyc, show y + q + t - z = (y - z) + q + t by ring] at hT
    rw [hxd, hyd, show y + t - z = (y - z) + t by ring] at hL
    exact BoundaryBlockAvoidance.no_tilted_normal_boundary hn' hk hkn hM hA hgap
      hp hq hr ht hperp hheight hB hR hT hL

/-- All Euclidean orientations are excluded, not only the axis-parallel ones. -/
theorem construction_avoids {n : ℕ} (hn : 3 ≤ n) :
    ¬ HasMonoRectangle (construction n) := by
  intro h
  rcases mono_rectangle_parameters h with haxis | htilt
  · exact construction_not_axis n haxis
  · exact construction_not_tilted hn htilt

end RectangleColoring
