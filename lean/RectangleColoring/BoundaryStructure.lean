import RectangleColoring.LocalAvoidance

namespace RectangleColoring.BoundaryStructure

/-- Ordinary points of the same color in two successive, non-wrapping blocks. -/
def BoundaryOrdinary (k A M x y : ℤ) : Prop :=
  (x = k + 1 ∧ y < A) ∨
  (x = k ∧ A ≤ y ∧ y < M + A - k) ∨
  (x = k - 1 ∧ M + A - k ≤ y)

/-- Special points of the same color in two successive, non-wrapping blocks. -/
def BoundarySpecial (n k M x y : ℤ) : Prop :=
  (k + 1 ≤ x ∧ x ≤ n ∧ 2 * y = x * (x - 1) + 2 * k) ∨
  (k ≤ x ∧ x ≤ n ∧ 2 * y = 2 * M + x * (x - 1) + 2 * (k - 1))

theorem parameters_order {n k A M : ℤ}
    (hn : 3 ≤ n) (hk : 1 ≤ k) (hkn : k < n)
    (hM : 2 * M = n * (n + 1)) (hA : 2 * A = k * (k + 1)) :
    k ≤ A ∧ A ≤ M ∧ k ≤ M := by
  have h₁ : 0 ≤ k * (k - 1) := mul_nonneg (by omega) (by omega)
  have h₂ : 0 ≤ (n - k) * (n + k + 1) := mul_nonneg (by omega) (by omega)
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem ordinary_antitone {k A M x y x' y' : ℤ} (hkM : k ≤ M)
    (h : BoundaryOrdinary k A M x y) (h' : BoundaryOrdinary k A M x' y')
    (hy : y < y') : x' ≤ x := by
  rcases h with ⟨hx, hy⟩ | ⟨hx, hy₁, hy₂⟩ | ⟨hx, hy⟩ <;>
    rcases h' with ⟨hx', hy'⟩ | ⟨hx', hy₁', hy₂'⟩ | ⟨hx', hy'⟩ <;> omega

/-- A window shorter than `M-n+1` cannot see both extreme ordinary columns. -/
theorem ordinary_width {n k A M lo hi H x y x' y' : ℤ}
    (hkn : k < n) (hH : H < M - n + 1) (hwindow : hi - lo ≤ H)
    (hlo : lo ≤ y) (hhi : y ≤ hi) (hlo' : lo ≤ y') (hhi' : y' ≤ hi)
    (h : BoundaryOrdinary k A M x y) (h' : BoundaryOrdinary k A M x' y') :
    |x - x'| ≤ 1 := by
  apply abs_le.mpr
  rcases h with ⟨hx, hy⟩ | ⟨hx, hy₁, hy₂⟩ | ⟨hx, hy⟩ <;>
    rcases h' with ⟨hx', hy'⟩ | ⟨hx', hy₁', hy₂'⟩ | ⟨hx', hy'⟩ <;> omega

/-- Within a short window every ordinary point lies left of every special point. -/
theorem ordinary_le_special {n k A M lo hi H x y x' y' : ℤ}
    (hn : 1 ≤ n) (hA : 2 * A = k * (k + 1))
    (hH : H < M - n + 1) (hwindow : hi - lo ≤ H)
    (hlo : lo ≤ y) (hhi' : y' ≤ hi)
    (h : BoundaryOrdinary k A M x y) (h' : BoundarySpecial n k M x' y') :
    x ≤ x' := by
  rcases h with ⟨hx, hy⟩ | ⟨hx, hy₁, hy₂⟩ | ⟨hx, hy⟩
  · rcases h' with ⟨hx', hxn, he⟩ | ⟨hx', hxn, he⟩
    · omega
    · by_contra hbad
      have heq : x' = k := by omega
      rw [heq] at he
      have htime : y' = M + A - 1 := by nlinarith
      omega
  · rcases h' with ⟨hx', hxn, he⟩ | ⟨hx', hxn, he⟩ <;> omega
  · rcases h' with ⟨hx', hxn, he⟩ | ⟨hx', hxn, he⟩ <;> omega

/-- Join the geometric color descriptions from two successive blocks. -/
theorem blockColor_boundary {n k A M x y : ℤ}
    (hkA : k ≤ A) (hAM : A ≤ M) (hA : 2 * A = k * (k + 1)) (hxn : x ≤ n)
    (h : (0 ≤ y ∧ y < M ∧ LocalAvoidance.BlockColor k x y) ∨
      (M ≤ y ∧ y < 2 * M ∧ LocalAvoidance.BlockColor (k - 1) x (y - M))) :
    BoundaryOrdinary k A M x y ∨ BoundarySpecial n k M x y := by
  rcases h with ⟨hy₀, hyM, hc⟩ | ⟨hyM, hy₂M, hc⟩
  · rcases hc with ho | hs
    · left
      rcases ho with ⟨hx, ht⟩ | ⟨hx, ht⟩
      · left
        exact ⟨hx, by omega⟩
      · right
        left
        exact ⟨hx, by omega, by omega⟩
    · right
      left
      exact ⟨hs.1, hxn, hs.2⟩
  · rcases hc with ho | hs
    · left
      rcases ho with ⟨hx, ht⟩ | ⟨hx, ht⟩
      · right
        left
        refine ⟨by omega, by omega, ?_⟩
        nlinarith
      · right
        right
        refine ⟨hx, ?_⟩
        nlinarith
    · right
      right
      refine ⟨by have := hs.1; omega, hxn, ?_⟩
      have := hs.2
      nlinarith

theorem blockColor_boundary_of_parameters {n k A M x y : ℤ}
    (hn : 3 ≤ n) (hk : 1 ≤ k) (hkn : k < n)
    (hM : 2 * M = n * (n + 1)) (hA : 2 * A = k * (k + 1)) (hxn : x ≤ n)
    (h : (0 ≤ y ∧ y < M ∧ LocalAvoidance.BlockColor k x y) ∨
      (M ≤ y ∧ y < 2 * M ∧ LocalAvoidance.BlockColor (k - 1) x (y - M))) :
    BoundaryOrdinary k A M x y ∨ BoundarySpecial n k M x y := by
  have hp := parameters_order hn hk hkn hM hA
  exact blockColor_boundary hp.1 hp.2.1 hA hxn h

end RectangleColoring.BoundaryStructure
