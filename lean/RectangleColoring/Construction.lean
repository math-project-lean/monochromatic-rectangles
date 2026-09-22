import RectangleColoring.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Group.Fin.Basic

namespace RectangleColoring

/-- A row in one block is indexed by its repeated columns `a < b`. -/
abbrev RowPair (n : ℕ) := (b : Fin (n + 1)) × Fin b.val

theorem sum_fin_id (m : ℕ) : (∑ i : Fin m, i.val) = m.choose 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i) m, Finset.sum_range_id,
    Nat.choose_two_right]

/-- Increasing triangular enumeration of all column pairs. -/
def pairIndex (n : ℕ) : RowPair n ≃ Fin (blockSize n) :=
  finSigmaFinEquiv.trans (finCongr (sum_fin_id (n + 1)))

theorem pairIndex_val {n : ℕ} (r : RowPair n) :
    (pairIndex n r).val = r.1.val.choose 2 + r.2.val := by
  simp only [pairIndex, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
    finSigmaFinEquiv_apply, Fin.val_castLE]
  rw [sum_fin_id]

abbrev RowCode (n : ℕ) := Fin n × RowPair n

/-- Blocks and triangular row indices enumerate the actual vertical coordinates. -/
def rowIndex (n : ℕ) : RowCode n ≃ Fin (n * blockSize n) :=
  (Equiv.prodCongr (Equiv.refl _) (pairIndex n)).trans finProdFinEquiv

theorem rowIndex_val {n : ℕ} (s : Fin n) (r : RowPair n) :
    (rowIndex n (s, r)).val = s.val * blockSize n + r.1.val.choose 2 + r.2.val := by
  simp [rowIndex, pairIndex_val, Nat.mul_comm, Nat.add_assoc, Nat.add_comm]

/-- The base row is `0, ..., n-1` with an extra copy of `a` at column `b`. -/
def rowBaseColor {n : ℕ} (r : RowPair n) (x : Fin (n + 1)) : Fin n :=
  if h : x.val < r.1.val then ⟨x.val, by omega⟩
  else if h' : x.val = r.1.val then ⟨r.2.val, by have := r.2.isLt; omega⟩
  else ⟨x.val - 1, by have := r.2.isLt; omega⟩

/-- Add the block number cyclically to all colors. -/
def rowColor {n : ℕ} (s : Fin n) (r : RowPair n) (x : Fin (n + 1)) : Fin n :=
  rowBaseColor r x + s

/-- Explicit coloring on `n * choose (n+1) 2` rows. -/
def construction (n : ℕ) : Coloring n (n * blockSize n) := fun p =>
  let code := (rowIndex n).symm p.2
  rowColor code.1 code.2 p.1

@[simp] theorem construction_rowIndex {n : ℕ} (s : Fin n) (r : RowPair n)
    (x : Fin (n + 1)) :
    construction n (x, rowIndex n (s, r)) = rowColor s r x := by
  simp [construction]

theorem rowBaseColor_eq_iff {n : ℕ} (r : RowPair n) (x z : Fin (n + 1))
    (hxz : x < z) :
    rowBaseColor r x = rowBaseColor r z ↔ x.val = r.2.val ∧ z = r.1 := by
  have ha := r.2.isLt
  have hb := r.1.isLt
  have hx : x.val < z.val := hxz
  simp only [rowBaseColor]
  split_ifs <;> simp only [Fin.mk.injEq] <;> constructor <;> intro h
  all_goals try { rcases h with ⟨h₁, h₂⟩; have := congrArg Fin.val h₂; omega }
  all_goals try omega

theorem rowColor_eq_iff {n : ℕ} (s : Fin n) (r : RowPair n)
    (x z : Fin (n + 1)) (hxz : x < z) :
    rowColor s r x = rowColor s r z ↔ x.val = r.2.val ∧ z = r.1 := by
  have hn : 0 < n := by have := s.isLt; omega
  letI : NeZero n := ⟨by omega⟩
  rw [rowColor, rowColor, add_right_cancel_iff, rowBaseColor_eq_iff r x z hxz]

theorem rowBaseColor_membership {n : ℕ} (r : RowPair n)
    (x : Fin (n + 1)) (k : Fin n) :
    rowBaseColor r x = k ↔
      (x = r.1 ∧ r.2.val = k.val) ∨
      (x.val < r.1.val ∧ x.val = k.val) ∨
      (r.1.val < x.val ∧ x.val = k.val + 1) := by
  have ha := r.2.isLt
  simp only [rowBaseColor, Fin.ext_iff]
  split_ifs <;> simp only <;> omega

theorem rowPair_eq_of_repeat {n : ℕ} (r q : RowPair n)
    (x z : Fin (n + 1))
    (hr : x.val = r.2.val ∧ z = r.1)
    (hq : x.val = q.2.val ∧ z = q.1) : r = q := by
  rcases r with ⟨b, a⟩
  rcases q with ⟨d, c⟩
  rcases hr with ⟨ha, hb⟩
  rcases hq with ⟨hc, hd⟩
  dsimp at ha hb hc hd
  subst b
  subst d
  have h : a = c := Fin.ext (ha.symm.trans hc)
  subst c
  rfl

/-- A column pair and a color occur together in at most one row. -/
theorem construction_pair_unique {n : ℕ} (x z : Fin (n + 1)) (hxz : x < z)
    (y t : Fin (n * blockSize n))
    (hy : construction n (x, y) = construction n (z, y))
    (ht : construction n (x, t) = construction n (z, t))
    (hyt : construction n (x, y) = construction n (x, t)) : y = t := by
  obtain ⟨⟨s, r⟩, rfl⟩ := (rowIndex n).surjective y
  obtain ⟨⟨v, q⟩, rfl⟩ := (rowIndex n).surjective t
  simp only [construction_rowIndex] at hy ht hyt
  have hr := (rowColor_eq_iff s r x z hxz).mp hy
  have hq := (rowColor_eq_iff v q x z hxz).mp ht
  have hrq := rowPair_eq_of_repeat r q x z hr hq
  subst q
  have hn : 0 < n := by have := s.isLt; omega
  letI : NeZero n := ⟨by omega⟩
  have hsv : s = v := add_left_cancel hyt
  subst v
  rfl

/-- In particular, the construction has no axis-parallel monochromatic rectangle. -/
theorem construction_no_axis_rectangle {n : ℕ}
    (x z : Fin (n + 1)) (hxz : x < z)
    (y t : Fin (n * blockSize n)) (hyt : y ≠ t) :
    ¬ (construction n (x, y) = construction n (z, y) ∧
       construction n (x, t) = construction n (z, t) ∧
       construction n (x, y) = construction n (x, t)) := by
  rintro ⟨h₁, h₂, h₃⟩
  exact hyt (construction_pair_unique x z hxz y t h₁ h₂ h₃)

end RectangleColoring
