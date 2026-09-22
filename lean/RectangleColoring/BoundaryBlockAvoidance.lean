import RectangleColoring.BoundaryAvoidance
import RectangleColoring.BoundaryStructure
import RectangleColoring.BoundarySparse

namespace RectangleColoring.BoundaryBlockAvoidance

open BoundaryStructure BoundarySparse

/-- The explicit ordinary/special point sets across a non-wrapping block
boundary contain no tilted rectangle of the indicated height. -/
theorem no_tilted_normal_boundary
    {n k M A H x y p q r t : ℤ}
    (hn : 3 ≤ n) (hk : 1 ≤ k) (hkn : k < n)
    (hM : 2 * M = n * (n + 1)) (hA : 2 * A = k * (k + 1))
    (hgap : H < M - n + 1)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (ht : 0 < t)
    (hperp : q * t = p * r) (hheight : q + t ≤ H)
    (hB : BoundaryOrdinary k A M (x + r) y ∨
      BoundarySpecial n k M (x + r) y)
    (hR : BoundaryOrdinary k A M (x + r + p) (y + q) ∨
      BoundarySpecial n k M (x + r + p) (y + q))
    (hT : BoundaryOrdinary k A M (x + p) (y + q + t) ∨
      BoundarySpecial n k M (x + p) (y + q + t))
    (hL : BoundaryOrdinary k A M x (y + t) ∨
      BoundarySpecial n k M x (y + t)) : False := by
  let O : ℤ → ℤ → Prop := fun u v =>
    BoundaryOrdinary k A M u v ∧ y ≤ v ∧ v ≤ y + q + t
  let S : ℤ → ℤ → Prop := fun u v =>
    BoundarySpecial n k M u v ∧ y ≤ v ∧ v ≤ y + q + t
  have hkM : k ≤ M := (parameters_order hn hk hkn hM hA).2.2
  have hwindow : y + q + t - y ≤ H := by omega
  have hB' : O (x + r) y ∨ S (x + r) y := by
    rcases hB with h | h
    · exact Or.inl ⟨h, by omega, by omega⟩
    · exact Or.inr ⟨h, by omega, by omega⟩
  have hR' : O (x + r + p) (y + q) ∨ S (x + r + p) (y + q) := by
    rcases hR with h | h
    · exact Or.inl ⟨h, by omega, by omega⟩
    · exact Or.inr ⟨h, by omega, by omega⟩
  have hT' : O (x + p) (y + q + t) ∨ S (x + p) (y + q + t) := by
    rcases hT with h | h
    · exact Or.inl ⟨h, by omega, by omega⟩
    · exact Or.inr ⟨h, by omega, by omega⟩
  have hL' : O x (y + t) ∨ S x (y + t) := by
    rcases hL with h | h
    · exact Or.inl ⟨h, by omega, by omega⟩
    · exact Or.inr ⟨h, by omega, by omega⟩
  apply BoundaryAvoidance.no_tilted (O := O) (S := S)
    hn hp hq hr ht hperp hheight hgap
    (hB := hB') (hR := hR') (hT := hT') (hL := hL')
  · intro xa ya xb yb ha hb hy
    exact ordinary_antitone hkM ha.1 hb.1 hy
  · intro xa ya xb yb ha hb
    have h := ordinary_width hkn hgap hwindow ha.2.1 ha.2.2 hb.2.1 hb.2.2 ha.1 hb.1
    have hle := (abs_le.mp h).2
    omega
  · intro xa ya xb yb ha hb
    exact ordinary_le_special (by omega) hA hgap hwindow ha.2.1 hb.2.2 ha.1 hb.1
  · intro xa ya xb yb ha hb hx hy
    exact sparse_pos hn hk hM ha.1 hb.1 hx hy
  · intro xa ya xb yb ha hb hx hy he
    exact sparse_pos_eq hn hk hM ha.1 hb.1 hx hy he
  · intro xa ya xb yb ha hb hx hy
    exact sparse_neg hn hk hM ha.1 hb.1 hx hy
  · intro xa ya xb yb ha hb hx hy he
    exact sparse_neg_eq hn hk hM ha.1 hb.1 hx hy he
  · intro xa ya xb yb ha hb hx hy
    exact sparse_neg_gap hn hk hM ha.1 hb.1 hx hy

end RectangleColoring.BoundaryBlockAvoidance
