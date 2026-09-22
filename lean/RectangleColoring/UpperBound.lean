import RectangleColoring.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.Fintype.Pigeonhole

namespace RectangleColoring

/-- Distinct rows and columns form an axis-parallel Euclidean rectangle. -/
theorem axis_isRectangle {n l : ℕ} {i j : Fin (n + 1)} {r s : Fin l}
    (hij : i ≠ j) (hrs : r ≠ s) :
    IsRectangle (i, r) (j, r) (j, s) (i, s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => hij (congrArg Prod.fst h)
  · exact fun h => hrs (congrArg Prod.snd h)
  · simp [xCoord, add_comm]
  · simp [yCoord]
  · simp [xCoord, yCoord]

/-- The pigeonhole bound already forces an axis-parallel monochromatic rectangle.
The record attached to a row consists of a repeated color and an unordered pair
of distinct columns. There are exactly `n * (n + 1).choose 2` records. -/
theorem upper_bound (n : ℕ) : ForcesRectangle n (threshold n) := by
  classical
  intro f
  have hrow : ∀ r : Fin (threshold n),
      ∃ i j : Fin (n + 1), i ≠ j ∧ f (i, r) = f (j, r) := by
    intro r
    exact Fintype.exists_ne_map_eq_of_card_lt (fun i => f (i, r)) (by simp)
  choose i j hij hcolor using hrow
  let Pair := {p : Sym2 (Fin (n + 1)) // ¬p.IsDiag}
  let record : Fin (threshold n) → Fin n × Pair := fun r =>
    (f (i r, r), ⟨s(i r, j r), by simpa using hij r⟩)
  have hcard : Fintype.card Pair = blockSize n := by
    simpa [Pair, blockSize] using
      (Sym2.card_subtype_not_diag (α := Fin (n + 1)))
  have hbound : Fintype.card (Fin n × Pair) <
      Fintype.card (Fin (threshold n)) := by
    rw [Fintype.card_prod, Fintype.card_fin, hcard, Fintype.card_fin]
    exact Nat.lt_succ_self _
  obtain ⟨r, s, hrs, hrecord⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt record hbound
  have hc : f (i r, r) = f (i s, s) := congrArg Prod.fst hrecord
  have hp : s(i r, j r) = s(i s, j s) :=
    congrArg (fun q : Fin n × Pair => q.2.val) hrecord
  have hi : f (i r, r) = f (i r, s) := by
    rcases Sym2.eq_iff.mp hp with ⟨hi, _⟩ | ⟨hi, _⟩
    · simpa only [hi] using hc
    · simpa only [hi] using hc.trans (hcolor s)
  have hj : f (i r, r) = f (j r, s) := by
    rcases Sym2.eq_iff.mp hp with ⟨_, hj⟩ | ⟨_, hj⟩
    · simpa only [hj] using hc.trans (hcolor s)
    · simpa only [hj] using hc
  exact ⟨(i r, r), (j r, r), (j r, s), (i r, s),
    axis_isRectangle (hij r) hrs, hcolor r, hj, hi⟩

end RectangleColoring
