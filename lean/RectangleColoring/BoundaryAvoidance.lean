import Mathlib.Tactic

/-!
The geometric core of the normal block-boundary argument.  The hypotheses are
pointwise arithmetic properties of ordinary and special points in the relevant
height interval.  This file separates the short rectangle argument from the
polynomial arithmetic establishing those properties for the construction.
-/

namespace RectangleColoring.BoundaryAvoidance

/-- If perpendicular edges both have slope magnitude at least one, both slopes
have magnitude exactly one. -/
theorem slopes_eq_one {p q r t : ℤ}
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (_ht : 0 < t)
    (hperp : q * t = p * r) (hpq : p ≤ q) (hrt : r ≤ t) :
    p = q ∧ r = t := by
  have hmul : p * r ≤ p * t := mul_le_mul_of_nonneg_left hrt (by omega)
  have hqp : q ≤ p := by nlinarith
  have hpq' : p = q := by omega
  subst q
  constructor
  · rfl
  · nlinarith

/-- A tilted rectangle cannot cross a normal color transition `k → k - 1`.
The ordinary and special predicates are restricted to the rectangle's height
interval before applying this lemma. -/
theorem no_tilted
    {O S : ℤ → ℤ → Prop} {n M H x y p q r t : ℤ}
    (hn : 3 ≤ n)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (ht : 0 < t)
    (hperp : q * t = p * r)
    (hheight : q + t ≤ H) (hgap : H < M - n + 1)
    (hOmono : ∀ {xa ya xb yb}, O xa ya → O xb yb → ya < yb → xb ≤ xa)
    (hOwidth : ∀ {xa ya xb yb}, O xa ya → O xb yb → xa ≤ xb + 1)
    (hOS : ∀ {xa ya xb yb}, O xa ya → S xb yb → xa ≤ xb)
    (hSpos : ∀ {xa ya xb yb}, S xa ya → S xb yb →
      xa < xb → ya < yb → xb - xa ≤ yb - ya)
    (hSposEq : ∀ {xa ya xb yb}, S xa ya → S xb yb →
      xa < xb → ya < yb → xb - xa = yb - ya → xa = 1 ∧ xb = 2)
    (hSneg : ∀ {xa ya xb yb}, S xa ya → S xb yb →
      xb < xa → ya < yb → xa - xb ≤ yb - ya)
    (hSnegEq : ∀ {xa ya xb yb}, S xa ya → S xb yb →
      xb < xa → ya < yb → xa - xb = yb - ya → xa = n ∧ xb = 1)
    (hSnegGap : ∀ {xa ya xb yb}, S xa ya → S xb yb →
      xa = xb + 1 → ya < yb → M - n ≤ yb - ya)
    (hB : O (x + r) y ∨ S (x + r) y)
    (hR : O (x + r + p) (y + q) ∨ S (x + r + p) (y + q))
    (hT : O (x + p) (y + q + t) ∨ S (x + p) (y + q + t))
    (hL : O x (y + t) ∨ S x (y + t)) : False := by
  have hTS : S (x + p) (y + q + t) := by
    rcases hT with hTO | hTS
    · rcases hL with hLO | hLS
      · have := hOmono hLO hTO (by omega)
        omega
      · have := hOS hTO hLS
        omega
    · exact hTS
  have hRS : S (x + r + p) (y + q) := by
    rcases hR with hRO | hRS
    · have := hOS hRO hTS
      omega
    · exact hRS
  have hrt : r ≤ t := by
    have := hSneg hRS hTS (by omega) (by omega)
    omega
  have hLO : O x (y + t) := by
    rcases hL with hLO | hLS
    · exact hLO
    · have hpq : p ≤ q := by
        have := hSpos hLS hTS (by omega) (by omega)
        omega
      obtain ⟨hpq', hrt'⟩ := slopes_eq_one hp hq hr ht hperp hpq hrt
      have he₁ := hSposEq hLS hTS (by omega) (by omega) (by omega)
      have he₂ := hSnegEq hRS hTS (by omega) (by omega) (by omega)
      omega
  have hBO : O (x + r) y := by
    rcases hB with hBO | hBS
    · exact hBO
    · have hpq : p ≤ q := by
        have := hSpos hBS hRS (by omega) (by omega)
        omega
      obtain ⟨hpq', hrt'⟩ := slopes_eq_one hp hq hr ht hperp hpq hrt
      have he₁ := hSposEq hBS hRS (by omega) (by omega) (by omega)
      have he₂ := hSnegEq hRS hTS (by omega) (by omega) (by omega)
      omega
  have hr1 : r = 1 := by
    have := hOwidth hBO hLO
    omega
  have htgap : M - n ≤ t := by
    have := hSnegGap hRS hTS (by omega) (by omega)
    omega
  omega

end RectangleColoring.BoundaryAvoidance
