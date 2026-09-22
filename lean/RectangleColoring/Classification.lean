import RectangleColoring.Construction
import RectangleColoring.LocalAvoidance

namespace RectangleColoring

/-- The triangular row enumeration as a division-free integer equation. -/
theorem twice_choose_two_int (b : ℕ) :
    2 * (b.choose 2 : ℤ) = (b : ℤ) * ((b : ℤ) - 1) := by
  induction b with
  | zero => norm_num
  | succ b ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast
    nlinarith

/-- Each occurrence of a base color is an ordinary or a special point. -/
theorem rowBaseColor_blockColor {n : ℕ} (r : RowPair n)
    (x : Fin (n + 1)) (k : Fin n) (hc : rowBaseColor r x = k) :
    LocalAvoidance.BlockColor (k.val : ℤ) (x.val : ℤ)
      ((r.1.val.choose 2 : ℤ) + (r.2.val : ℤ)) := by
  apply LocalAvoidance.blockColor_of_row (a := (r.2.val : ℤ)) (b := (r.1.val : ℤ))
  · positivity
  · exact_mod_cast r.2.isLt
  · positivity
  · have ht := twice_choose_two_int r.1.val
    nlinarith
  · rcases (rowBaseColor_membership r x k).mp hc with
      ⟨hxb, hak⟩ | ⟨hxb, hxk⟩ | ⟨hbx, hxk⟩
    · right
      left
      constructor
      · exact_mod_cast congrArg Fin.val hxb
      · exact_mod_cast hak.symm
    · left
      constructor
      · exact_mod_cast hxb
      · exact_mod_cast hxk.symm
    · right
      right
      constructor
      · exact_mod_cast hbx
      · have hxk' : (x.val : ℤ) = (k.val : ℤ) + 1 := by exact_mod_cast hxk
        omega

/-- Undoing the cyclic shift recovers the base color in a given block. -/
theorem rowColor_eq_iff_baseColor {n : ℕ} (s : Fin n) (r : RowPair n)
    (x : Fin (n + 1)) (c : Fin n) :
    rowColor s r x = c ↔ rowBaseColor r x = c - s := by
  have hn : n ≠ 0 := by have := s.isLt; omega
  letI : NeZero n := ⟨hn⟩
  exact eq_sub_iff_add_eq.symm

/-- Geometric color membership after accounting for the block's cyclic shift. -/
theorem rowColor_blockColor {n : ℕ} (s : Fin n) (r : RowPair n)
    (x : Fin (n + 1)) (c : Fin n) (hc : rowColor s r x = c) :
    LocalAvoidance.BlockColor ((c - s).val : ℤ) (x.val : ℤ)
      ((r.1.val.choose 2 : ℤ) + (r.2.val : ℤ)) :=
  rowBaseColor_blockColor r x (c - s) ((rowColor_eq_iff_baseColor s r x c).mp hc)

/-- In global coordinates, subtracting the start of a block gives its local height. -/
theorem construction_rowIndex_blockColor {n : ℕ} (s : Fin n) (r : RowPair n)
    (x : Fin (n + 1)) (c : Fin n)
    (hc : construction n (x, rowIndex n (s, r)) = c) :
    LocalAvoidance.BlockColor ((c - s).val : ℤ) (x.val : ℤ)
      (((rowIndex n (s, r)).val : ℤ) - (s.val : ℤ) * (blockSize n : ℤ)) := by
  have h := rowColor_blockColor s r x c (by simpa using hc)
  rw [rowIndex_val]
  push_cast
  convert h using 1
  ring

/-- A fixed global color decreases its local color by one at an ordinary boundary. -/
theorem localColor_next_block_of_pos {n : ℕ} (c s t : Fin n)
    (hst : t.val = s.val + 1) (hc : 0 < (c - s).val) :
    (c - t).val + 1 = (c - s).val := by
  have hs := Fin.intCast_val_sub_eq_sub_add_ite c s
  have ht := Fin.intCast_val_sub_eq_sub_add_ite c t
  split_ifs at hs ht <;> simp only [Fin.le_iff_val_le_val] at * <;> omega

/-- At the cyclic boundary the local color changes from zero to `n-1`. -/
theorem localColor_next_block_of_zero {n : ℕ} (c s t : Fin n)
    (hst : t.val = s.val + 1) (hc : (c - s).val = 0) :
    (c - t).val = n - 1 := by
  have hs := Fin.intCast_val_sub_eq_sub_add_ite c s
  have ht := Fin.intCast_val_sub_eq_sub_add_ite c t
  split_ifs at hs ht <;> simp only [Fin.le_iff_val_le_val] at * <;> omega

/-- The block containing a point of the explicit construction. -/
def blockOf {n : ℕ} (p : Grid n (n * blockSize n)) : Fin n :=
  ((rowIndex n).symm p.2).1

/-- The height measured from the bottom row of the point's block. -/
def localHeight {n : ℕ} (p : Grid n (n * blockSize n)) : ℤ :=
  yCoord p - ((blockOf p).val : ℤ) * (blockSize n : ℤ)

/-- The color classification directly for a point of the actual grid. -/
theorem construction_point_blockColor {n : ℕ} (p : Grid n (n * blockSize n))
    (c : Fin n) (hc : construction n p = c) :
    LocalAvoidance.BlockColor ((c - blockOf p).val : ℤ) (xCoord p) (localHeight p) := by
  rcases p with ⟨x, y⟩
  obtain ⟨⟨s, r⟩, rfl⟩ := (rowIndex n).surjective y
  simpa only [blockOf, localHeight, Equiv.symm_apply_apply, xCoord, yCoord] using
    construction_rowIndex_blockColor s r x c hc

/-- The local height lies in the half-open interval of one block. -/
theorem localHeight_bounds {n : ℕ} (p : Grid n (n * blockSize n)) :
    0 ≤ localHeight p ∧ localHeight p < (blockSize n : ℤ) := by
  rcases p with ⟨x, y⟩
  obtain ⟨⟨s, r⟩, rfl⟩ := (rowIndex n).surjective y
  simp only [localHeight, blockOf, Equiv.symm_apply_apply, yCoord, rowIndex_val]
  have hp := (pairIndex n r).isLt
  rw [pairIndex_val] at hp
  push_cast
  constructor <;> omega

/-- All points in a vertical band shorter than one block meet at most two blocks. -/
theorem blockOf_band {n : ℕ} (a p : Grid n (n * blockSize n))
    (hlo : yCoord a ≤ yCoord p)
    (hhi : yCoord p - yCoord a < (blockSize n : ℤ)) :
    blockOf p = blockOf a ∨ (blockOf p).val = (blockOf a).val + 1 := by
  have ha := localHeight_bounds a
  have hp := localHeight_bounds p
  have hm : 0 < (blockSize n : ℤ) := by omega
  dsimp only [localHeight] at ha hp
  have hs : ((blockOf a).val : ℤ) ≤ ((blockOf p).val : ℤ) := by
    by_contra hn
    have hmul : 0 ≤ (((blockOf a).val : ℤ) - ((blockOf p).val : ℤ) - 1) *
        (blockSize n : ℤ) := mul_nonneg (by omega) (by omega)
    nlinarith
  have ht : ((blockOf p).val : ℤ) ≤ ((blockOf a).val : ℤ) + 1 := by
    by_contra hn
    have hmul : 0 ≤ (((blockOf p).val : ℤ) - ((blockOf a).val : ℤ) - 2) *
        (blockSize n : ℤ) := mul_nonneg (by omega) (by omega)
    nlinarith
  by_cases heq : (blockOf p).val = (blockOf a).val
  · exact Or.inl (Fin.ext heq)
  · exact Or.inr (by omega)

end RectangleColoring
