import Mathlib.Tactic

/-!
One-block avoidance in the explicit coloring.  In a fixed color class, ordinary
points move weakly left as height increases; special points move strictly right,
and every ordinary point lies to the left of every special point.  These facts
exclude even a downward peak, so no perpendicularity argument is needed here.
-/

namespace RectangleColoring.LocalAvoidance

/-- The two possible ordinary columns, with their exact transition height.
Doubling the height keeps the statement free of division. -/
def Ordinary (k x y : ℤ) : Prop :=
  (x = k + 1 ∧ 2 * y < k * (k + 1)) ∨
  (x = k ∧ k * (k + 1) ≤ 2 * y)

/-- Extra occurrences of a color lie on an integral parabola. -/
def Special (k x y : ℤ) : Prop :=
  k + 1 ≤ x ∧ 2 * y = x * (x - 1) + 2 * k

/-- A fixed color class in one block, using local vertical coordinates. -/
def BlockColor (k x y : ℤ) : Prop := Ordinary k x y ∨ Special k x y

/-- The elementary row rule really gives the declared geometric color class.
Here `a < b` is the duplicated pair and `y = choose b 2 + a`. -/
theorem blockColor_of_row {a b k x y : ℤ}
    (ha : 0 ≤ a) (hab : a < b) (hx : 0 ≤ x)
    (hy : 2 * y = b * (b - 1) + 2 * a)
    (hc : (x < b ∧ k = x) ∨ (x = b ∧ k = a) ∨ (b < x ∧ k = x - 1)) :
    BlockColor k x y := by
  rcases hc with ⟨hxb, hkx⟩ | ⟨hxb, hka⟩ | ⟨hbx, hkx⟩
  · subst k
    left
    right
    refine ⟨rfl, ?_⟩
    have hd : 0 ≤ (b - x - 1) * (b + x) :=
      mul_nonneg (by omega) (by omega)
    nlinarith
  · subst x
    subst k
    right
    exact ⟨by omega, hy⟩
  · subst k
    left
    left
    refine ⟨by omega, ?_⟩
    have hd : 0 ≤ (x - b - 1) * (x + b) :=
      mul_nonneg (by omega) (by omega)
    nlinarith

theorem ordinary_antitone {k x y x' y' : ℤ}
    (h : Ordinary k x y) (h' : Ordinary k x' y') (hy : y < y') : x' ≤ x := by
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
    rcases h' with ⟨h₃, h₄⟩ | ⟨h₃, h₄⟩ <;> omega

theorem special_strictMono {k x y x' y' : ℤ} (hk : 0 ≤ k)
    (h : Special k x y) (h' : Special k x' y') (hy : y < y') : x < x' := by
  rcases h with ⟨hx, he⟩
  rcases h' with ⟨hx', he'⟩
  by_contra hn
  have hd : 0 ≤ (x - x') * (x + x' - 1) :=
    mul_nonneg (by omega) (by omega)
  nlinarith

theorem ordinary_le_special {k x y x' y' : ℤ}
    (h : Ordinary k x y) (h' : Special k x' y') : x ≤ x' := by
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rcases h' with ⟨h₃, h₄⟩ <;> omega

/-- Two oppositely monotone separated chains cannot contain a downward peak:
one point above a left point and a right point. -/
theorem separated_chains_no_peak {O S : ℤ → ℤ → Prop}
    (hO : ∀ {x y x' y'}, O x y → O x' y' → y < y' → x' ≤ x)
    (hS : ∀ {x y x' y'}, S x y → S x' y' → y < y' → x < x')
    (hOS : ∀ {x y x' y'}, O x y → S x' y' → x ≤ x')
    {lx ly tx ty rx ry : ℤ}
    (hlt : lx < tx) (htr : tx < rx) (hly : ly < ty) (hry : ry < ty)
    (hl : O lx ly ∨ S lx ly) (ht : O tx ty ∨ S tx ty)
    (hr : O rx ry ∨ S rx ry) : False := by
  rcases ht with ht | ht
  · rcases hl with hl | hl
    · have := hO hl ht hly
      omega
    · have := hOS ht hl
      omega
  · rcases hr with hr | hr
    · have := hOS hr ht
      omega
    · have := hS hr ht hry
      omega

theorem blockColor_no_peak {k lx ly tx ty rx ry : ℤ} (hk : 0 ≤ k)
    (hlt : lx < tx) (htr : tx < rx) (hly : ly < ty) (hry : ry < ty)
    (hl : BlockColor k lx ly) (ht : BlockColor k tx ty)
    (hr : BlockColor k rx ry) : False := by
  exact separated_chains_no_peak ordinary_antitone (special_strictMono hk)
    ordinary_le_special hlt htr hly hry hl ht hr

/-- No tilted parallelogram (hence no tilted rectangle) lies in one block's
fixed color class.  The bottom vertex is not needed for this stronger result. -/
theorem blockColor_no_tilted {k x y p q r t : ℤ} (hk : 0 ≤ k)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (ht : 0 < t)
    (hR : BlockColor k (x + r + p) (y + q))
    (hT : BlockColor k (x + p) (y + q + t))
    (hL : BlockColor k x (y + t)) : False := by
  apply blockColor_no_peak hk (by omega) (by omega) (by omega) (by omega) hL hT hR

end RectangleColoring.LocalAvoidance
