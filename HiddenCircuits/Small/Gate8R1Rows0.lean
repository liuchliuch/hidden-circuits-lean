import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8R1Data

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise1_row0 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 0 b =
    (gate8FastCompound (gate8AddedBound 1) 0 b : ℤ) := by
  decide +kernel

theorem gate8_rise1_row1 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 1 b =
    (gate8FastCompound (gate8AddedBound 1) 1 b : ℤ) := by
  decide +kernel

theorem gate8_rise1_row2 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 2 b =
    (gate8FastCompound (gate8AddedBound 1) 2 b : ℤ) := by
  decide +kernel

theorem gate8_rise1_row3 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 3 b =
    (gate8FastCompound (gate8AddedBound 1) 3 b : ℤ) := by
  decide +kernel

theorem gate8_rise1_row4 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 4 b =
    (gate8FastCompound (gate8AddedBound 1) 4 b : ℤ) := by
  decide +kernel

theorem gate8_rise1_row5 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 5 b =
    (gate8FastCompound (gate8AddedBound 1) 5 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 5 5
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row6 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 6 b =
    (gate8FastCompound (gate8AddedBound 1) 6 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 6 6
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row7 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 7 b =
    (gate8FastCompound (gate8AddedBound 1) 7 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 7 7
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row8 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 8 b =
    (gate8FastCompound (gate8AddedBound 1) 8 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 8 8
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row9 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 9 b =
    (gate8FastCompound (gate8AddedBound 1) 9 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 9 9
    (by decide +kernel) (by decide +kernel)

end HiddenCircuits.Small
