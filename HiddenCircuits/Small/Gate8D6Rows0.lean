import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8D6Data

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_drop6_row0 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 0 b =
    (gate8FastCompound (gate8DeletedBound 6) 0 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 0 0
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row1 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 1 b =
    (gate8FastCompound (gate8DeletedBound 6) 1 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 1 1
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row2 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 2 b =
    (gate8FastCompound (gate8DeletedBound 6) 2 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 2 2
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row3 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 3 b =
    (gate8FastCompound (gate8DeletedBound 6) 3 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 3 4
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row4 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 4 b =
    (gate8FastCompound (gate8DeletedBound 6) 4 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 4 4
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row5 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 5 b =
    (gate8FastCompound (gate8DeletedBound 6) 5 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 5 5
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row6 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 6 b =
    (gate8FastCompound (gate8DeletedBound 6) 6 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 6 6
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row7 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 7 b =
    (gate8FastCompound (gate8DeletedBound 6) 7 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 7 8
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row8 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 8 b =
    (gate8FastCompound (gate8DeletedBound 6) 8 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 8 8
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row9 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 9 b =
    (gate8FastCompound (gate8DeletedBound 6) 9 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 9 9
    (by decide +kernel) (by decide +kernel)

end HiddenCircuits.Small
