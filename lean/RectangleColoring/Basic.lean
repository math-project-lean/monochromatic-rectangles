import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

namespace RectangleColoring

def blockSize (n : ℕ) : ℕ := (n + 1).choose 2

def threshold (n : ℕ) : ℕ := n * blockSize n + 1

abbrev Grid (n l : ℕ) := Fin (n + 1) × Fin l

abbrev Coloring (n l : ℕ) := Grid n l → Fin n

def xCoord {n l : ℕ} (p : Grid n l) : ℤ := p.1.val

def yCoord {n l : ℕ} (p : Grid n l) : ℤ := p.2.val

/-- Four cyclically ordered vertices of a nondegenerate Euclidean rectangle.
The equations express a parallelogram with perpendicular adjacent sides. -/
def IsRectangle {n l : ℕ} (a b c d : Grid n l) : Prop :=
  a ≠ b ∧ a ≠ d ∧
  xCoord a + xCoord c = xCoord b + xCoord d ∧
  yCoord a + yCoord c = yCoord b + yCoord d ∧
  (xCoord b - xCoord a) * (xCoord d - xCoord a) +
    (yCoord b - yCoord a) * (yCoord d - yCoord a) = 0

def HasMonoRectangle {n l : ℕ} (f : Coloring n l) : Prop :=
  ∃ a b c d, IsRectangle a b c d ∧
    f a = f b ∧ f a = f c ∧ f a = f d

def ForcesRectangle (n l : ℕ) : Prop :=
  ∀ f : Coloring n l, HasMonoRectangle f

def IsMinimum (n l : ℕ) : Prop :=
  ForcesRectangle n l ∧ ∀ k < l, ¬ ForcesRectangle n k

end RectangleColoring
