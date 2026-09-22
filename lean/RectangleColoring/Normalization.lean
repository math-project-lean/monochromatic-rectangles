import RectangleColoring.Basic

namespace RectangleColoring

def AxisMono {n l : ℕ} (f : Coloring n l) : Prop :=
  ∃ x₁ x₂ : Fin (n + 1), ∃ y₁ y₂ : Fin l,
    x₁ ≠ x₂ ∧ y₁ ≠ y₂ ∧
    f (x₁, y₁) = f (x₂, y₁) ∧
    f (x₁, y₁) = f (x₂, y₂) ∧
    f (x₁, y₁) = f (x₁, y₂)

theorem grid_ext {n l : ℕ} {a b : Grid n l}
    (hx : xCoord a = xCoord b) (hy : yCoord a = yCoord b) : a = b := by
  apply Prod.ext <;> apply Fin.ext
  · simpa [xCoord] using hx
  · simpa [yCoord] using hy

theorem rectangle_rotate {n l : ℕ} {a b c d : Grid n l}
    (h : IsRectangle a b c d) : IsRectangle b c d a := by
  rcases h with ⟨hab, had, hx, hy, hp⟩
  have hbc : b ≠ c := by
    intro he
    subst c
    apply had
    apply grid_ext <;> linarith
  refine ⟨hbc, Ne.symm hab, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · have hx' : xCoord c - xCoord b = xCoord d - xCoord a := by omega
    have hy' : yCoord c - yCoord b = yCoord d - yCoord a := by omega
    rw [hx', hy']
    nlinarith [hp]

theorem rectangle_reverse {n l : ℕ} {a b c d : Grid n l}
    (h : IsRectangle a b c d) : IsRectangle a d c b := by
  rcases h with ⟨hab, had, hx, hy, hp⟩
  refine ⟨had, hab, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · nlinarith [hp]

theorem rectangle_mono_min_vertex {n l : ℕ} {f : Coloring n l}
    (h : HasMonoRectangle f) :
    ∃ a b c d, IsRectangle a b c d ∧
      f a = f b ∧ f a = f c ∧ f a = f d ∧
      yCoord a ≤ yCoord b ∧ yCoord a ≤ yCoord d := by
  obtain ⟨a, b, c, d, hr, hab, hac, had⟩ := h
  have hr₂ := rectangle_rotate hr
  have hr₃ := rectangle_rotate hr₂
  have hr₄ := rectangle_rotate hr₃
  by_cases haby : yCoord a ≤ yCoord b
  · by_cases hady : yCoord a ≤ yCoord d
    · exact ⟨a, b, c, d, hr, hab, hac, had, haby, hady⟩
    · by_cases hdcy : yCoord d ≤ yCoord c
      · exact ⟨d, a, b, c, hr₄, had.symm, had.symm.trans hab,
          had.symm.trans hac, by omega, hdcy⟩
      · exact ⟨c, d, a, b, hr₃, hac.symm.trans had, hac.symm,
          hac.symm.trans hab, by omega, by omega⟩
  · by_cases hbcy : yCoord b ≤ yCoord c
    · exact ⟨b, c, d, a, hr₂, hab.symm.trans hac, hab.symm.trans had,
        hab.symm, hbcy, by omega⟩
    · have hy := hr.2.2.2.1
      exact ⟨c, d, a, b, hr₃, hac.symm.trans had, hac.symm,
        hac.symm.trans hab, by omega, by omega⟩

theorem horizontal_edge_axis {n l : ℕ} {f : Coloring n l}
    {a b c d : Grid n l} (hr : IsRectangle a b c d)
    (hab : f a = f b) (hac : f a = f c) (had : f a = f d)
    (hhor : yCoord a = yCoord b) : AxisMono f := by
  rcases hr with ⟨hne₁, hne₂, hx, hy, hp⟩
  have haxbx : xCoord a ≠ xCoord b := by
    intro he
    exact hne₁ (grid_ext he hhor)
  have haxdx : xCoord a = xCoord d := by
    have hz : (xCoord b - xCoord a) * (xCoord d - xCoord a) = 0 := by
      rw [← hhor] at hp
      simpa using hp
    rcases mul_eq_zero.mp hz with hz | hz
    · exact False.elim (haxbx (by omega))
    · omega
  have haydy : yCoord a ≠ yCoord d := by
    intro he
    exact hne₂ (grid_ext haxdx he)
  have hb : (b.1, a.2) = b := by
    apply grid_ext
    · rfl
    · exact hhor
  have hc : (b.1, d.2) = c := by
    apply grid_ext
    · change xCoord b = xCoord c
      omega
    · change yCoord d = yCoord c
      omega
  have hd : (a.1, d.2) = d := by
    apply grid_ext
    · exact haxdx
    · rfl
  refine ⟨a.1, b.1, a.2, d.2, ?_, ?_, ?_, ?_, ?_⟩
  · intro he
    apply haxbx
    simp [xCoord, he]
  · intro he
    apply haydy
    simp [yCoord, he]
  · simpa only [hb, Prod.mk.eta] using hab
  · simpa only [hc, Prod.mk.eta] using hac
  · simpa only [hd, Prod.mk.eta] using had

/-- A monochromatic rectangle is either axis aligned, or can be cyclically
relabelled so its bottom vertex has its next vertex strictly to the upper right
and its preceding vertex strictly to the upper left. -/
theorem mono_rectangle_normal_form {n l : ℕ} {f : Coloring n l}
    (h : HasMonoRectangle f) :
    AxisMono f ∨
    ∃ a b c d, IsRectangle a b c d ∧
      f a = f b ∧ f a = f c ∧ f a = f d ∧
      yCoord a < yCoord b ∧ yCoord a < yCoord d ∧
      xCoord d < xCoord a ∧ xCoord a < xCoord b := by
  obtain ⟨a, b, c, d, hr, hab, hac, had, hyb, hyd⟩ :=
    rectangle_mono_min_vertex h
  by_cases he₁ : yCoord a = yCoord b
  · exact Or.inl (horizontal_edge_axis hr hab hac had he₁)
  by_cases he₂ : yCoord a = yCoord d
  · exact Or.inl (horizontal_edge_axis (rectangle_reverse hr) had hac hab he₂)
  have hq : 0 < yCoord b - yCoord a := by omega
  have ht : 0 < yCoord d - yCoord a := by omega
  have hp := hr.2.2.2.2
  have hxprod : (xCoord b - xCoord a) * (xCoord d - xCoord a) < 0 := by
    have := mul_pos hq ht
    omega
  rcases (mul_neg_iff.mp hxprod) with ⟨hb, hd⟩ | ⟨hb, hd⟩
  · exact Or.inr ⟨a, b, c, d, hr, hab, hac, had, by omega, by omega,
      by omega, by omega⟩
  · exact Or.inr ⟨a, d, c, b, rectangle_reverse hr, had, hac, hab,
      by omega, by omega, by omega, by omega⟩

/-- Integer-coordinate parameters for a tilted monochromatic rectangle.
The four grid vertices certify the coordinate bounds without separate side
conditions. `a,b,c,d` are respectively bottom, right, top, and left. -/
def TiltedMono {n l : ℕ} (f : Coloring n l) : Prop :=
  ∃ a b c d : Grid n l, ∃ x y p q r t : ℤ,
    0 < p ∧ 0 < q ∧ 0 < r ∧ 0 < t ∧
    q * t = p * r ∧ p + r ≤ (n : ℤ) ∧
    xCoord a = x + r ∧ yCoord a = y ∧
    xCoord b = x + r + p ∧ yCoord b = y + q ∧
    xCoord c = x + p ∧ yCoord c = y + q + t ∧
    xCoord d = x ∧ yCoord d = y + t ∧
    f a = f b ∧ f a = f c ∧ f a = f d

/-- Every monochromatic Euclidean rectangle admits the usual axis or tilted
normal form; the tilted form includes its perpendicularity and width bounds. -/
theorem mono_rectangle_parameters {n l : ℕ} {f : Coloring n l}
    (h : HasMonoRectangle f) : AxisMono f ∨ TiltedMono f := by
  rcases mono_rectangle_normal_form h with hax | htilt
  · exact Or.inl hax
  · right
    obtain ⟨a, b, c, d, hr, hab, hac, had, hyb, hyd, hxd, hxb⟩ := htilt
    rcases hr with ⟨_, _, hx, hy, hp⟩
    have hbound : xCoord b ≤ (n : ℤ) := by
      dsimp [xCoord]
      exact_mod_cast Nat.le_of_lt_succ b.1.isLt
    have hnonneg : 0 ≤ xCoord d := by
      dsimp [xCoord]
      exact_mod_cast Nat.zero_le d.1.val
    refine ⟨a, b, c, d, xCoord d, yCoord a,
      xCoord b - xCoord a, yCoord b - yCoord a,
      xCoord a - xCoord d, yCoord d - yCoord a,
      by omega, by omega, by omega, by omega, ?_, by omega,
      by omega, rfl, by omega, by omega, by omega, by omega,
      rfl, by omega, hab, hac, had⟩
    nlinarith [hp]

end RectangleColoring
