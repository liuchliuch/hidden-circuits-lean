import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8R2Data

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise2_row0 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 0 b =
    (gate8FastCompound (gate8AddedBound 2) 0 b : ℤ) := by
  decide +kernel

theorem gate8_rise2_row1 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 1 b =
    (gate8FastCompound (gate8AddedBound 2) 1 b : ℤ) := by
  exact gate8_unit_row Gate8R2ZRows (gate8AddedBound 2) 1 1
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise2_row2 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 2 b =
    (gate8FastCompound (gate8AddedBound 2) 2 b : ℤ) := by
  exact gate8_unit_row Gate8R2ZRows (gate8AddedBound 2) 2 2
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise2_row3 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 3 b =
    (gate8FastCompound (gate8AddedBound 2) 3 b : ℤ) := by
  exact gate8_unit_row Gate8R2ZRows (gate8AddedBound 2) 3 3
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise2_row4 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 4 b =
    (gate8FastCompound (gate8AddedBound 2) 4 b : ℤ) := by
  exact gate8_unit_row Gate8R2ZRows (gate8AddedBound 2) 4 4
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise2_row5 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 5 b =
    (gate8FastCompound (gate8AddedBound 2) 5 b : ℤ) := by
  exact gate8_unit_row Gate8R2ZRows (gate8AddedBound 2) 5 1
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise2_row6 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 6 b =
    (gate8FastCompound (gate8AddedBound 2) 6 b : ℤ) := by
  exact gate8_unit_row Gate8R2ZRows (gate8AddedBound 2) 6 2
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise2_row7 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 7 b =
    (gate8FastCompound (gate8AddedBound 2) 7 b : ℤ) := by
  exact gate8_unit_row Gate8R2ZRows (gate8AddedBound 2) 7 3
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise2_row8 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 8 b =
    (gate8FastCompound (gate8AddedBound 2) 8 b : ℤ) := by
  exact gate8_unit_row Gate8R2ZRows (gate8AddedBound 2) 8 4
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise2_row9 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 9 b =
    (gate8FastCompound (gate8AddedBound 2) 9 b : ℤ) := by
  exact gate8_unit_row Gate8R2ZRows (gate8AddedBound 2) 9 9
    (by decide +kernel) (by decide +kernel)

end HiddenCircuits.Small
