import RectangleColoring.UpperBound

namespace RectangleColoring

/-- Include a shorter grid in a taller grid, keeping both coordinates unchanged. -/
def embedHeight {n l L : ℕ} (h : l ≤ L) (p : Grid n l) : Grid n L :=
  (p.1, p.2.castLE h)

theorem embedHeight_injective {n l L : ℕ} (h : l ≤ L) :
    Function.Injective (@embedHeight n l L h) := by
  intro a b hab
  apply Prod.ext
  · exact congrArg (fun p : Grid n L => p.1) hab
  · apply Fin.ext
    exact congrArg (fun p : Grid n L => p.2.val) hab

theorem isRectangle_embedHeight {n l L : ℕ} (h : l ≤ L)
    {a b c d : Grid n l} (hr : IsRectangle a b c d) :
    IsRectangle (embedHeight h a) (embedHeight h b)
      (embedHeight h c) (embedHeight h d) := by
  rcases hr with ⟨hab, had, hx, hy, hperp⟩
  exact ⟨fun he => hab (embedHeight_injective h he),
    fun he => had (embedHeight_injective h he), hx, hy, hperp⟩

/-- If every coloring of a grid has a rectangle, adding rows preserves this fact. -/
theorem forcesRectangle_mono {n l L : ℕ} (h : l ≤ L)
    (hf : ForcesRectangle n l) : ForcesRectangle n L := by
  intro f
  obtain ⟨a, b, c, d, hr, hc⟩ := hf (fun p => f (embedHeight h p))
  exact ⟨embedHeight h a, embedHeight h b, embedHeight h c, embedHeight h d,
    isRectangle_embedHeight h hr, hc⟩

theorem not_forcesRectangle_of_le {n l L : ℕ} (h : l ≤ L)
    (hf : ¬ ForcesRectangle n L) : ¬ ForcesRectangle n l :=
  fun hl => hf (forcesRectangle_mono h hl)

def oneColorOneRow : Coloring 1 1 := fun _ => 0

theorem oneColorOneRow_avoids : ¬ HasMonoRectangle oneColorOneRow := by
  unfold HasMonoRectangle IsRectangle xCoord yCoord
  decide +kernel

theorem oneColor_lower : ¬ ForcesRectangle 1 1 :=
  fun h => oneColorOneRow_avoids (h oneColorOneRow)

/-- Rows, from bottom to top: 001, 010, 011, 110, 101, 100. -/
def twoColorSixRows : Coloring 2 6 := fun p =>
  if p.2.val = 0 then (if p.1.val = 2 then 1 else 0)
  else if p.2.val = 1 then (if p.1.val = 1 then 1 else 0)
  else if p.2.val = 2 then (if p.1.val = 0 then 0 else 1)
  else if p.2.val = 3 then (if p.1.val = 2 then 0 else 1)
  else if p.2.val = 4 then (if p.1.val = 1 then 0 else 1)
  else (if p.1.val = 0 then 1 else 0)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem twoColorSixRows_avoids : ¬ HasMonoRectangle twoColorSixRows := by
  have checked : ∀ a b : Grid 2 6,
      twoColorSixRows a = twoColorSixRows b →
      ∀ c : Grid 2 6,
      twoColorSixRows a = twoColorSixRows c →
      ∀ d : Grid 2 6,
      twoColorSixRows a = twoColorSixRows d → ¬ IsRectangle a b c d := by
    unfold IsRectangle xCoord yCoord
    dsimp only [Grid]
    simp only [Prod.forall]
    decide +kernel
  rintro ⟨a, b, c, d, hr, hab, hac, had⟩
  exact checked a b hab c hac d had hr

theorem twoColor_lower : ¬ ForcesRectangle 2 6 :=
  fun h => twoColorSixRows_avoids (h twoColorSixRows)

theorem oneColor_minimum : IsMinimum 1 2 := by
  constructor
  · simpa [threshold, blockSize] using upper_bound 1
  · intro k hk
    exact not_forcesRectangle_of_le (by omega) oneColor_lower

theorem twoColor_minimum : IsMinimum 2 7 := by
  constructor
  · simpa [threshold, blockSize] using upper_bound 2
  · intro k hk
    exact not_forcesRectangle_of_le (by omega) twoColor_lower

#print axioms oneColor_minimum
#print axioms twoColor_minimum

end RectangleColoring
