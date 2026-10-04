import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8R3Data

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise3_row0 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 0 b =
    (gate8FastCompound (gate8AddedBound 3) 0 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 0 0
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row1 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 1 b =
    (gate8FastCompound (gate8AddedBound 3) 1 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 1 0
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row2 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 2 b =
    (gate8FastCompound (gate8AddedBound 3) 2 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 2 2
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row3 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 3 b =
    (gate8FastCompound (gate8AddedBound 3) 3 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 3 3
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row4 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 4 b =
    (gate8FastCompound (gate8AddedBound 3) 4 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 4 4
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row5 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 5 b =
    (gate8FastCompound (gate8AddedBound 3) 5 b : ℤ) := by
  decide +kernel

theorem gate8_rise3_row6 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 6 b =
    (gate8FastCompound (gate8AddedBound 3) 6 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 6 6
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row7 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 7 b =
    (gate8FastCompound (gate8AddedBound 3) 7 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 7 7
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row8 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 8 b =
    (gate8FastCompound (gate8AddedBound 3) 8 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 8 8
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row9 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 9 b =
    (gate8FastCompound (gate8AddedBound 3) 9 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 9 6
    (by decide +kernel) (by decide +kernel)

end HiddenCircuits.Small
