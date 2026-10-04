import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8R4Data

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise4_row0 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 0 b =
    (gate8FastCompound (gate8AddedBound 4) 0 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 0 0
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row1 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 1 b =
    (gate8FastCompound (gate8AddedBound 4) 1 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 1 1
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row2 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 2 b =
    (gate8FastCompound (gate8AddedBound 4) 2 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 2 1
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row3 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 3 b =
    (gate8FastCompound (gate8AddedBound 4) 3 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 3 3
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row4 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 4 b =
    (gate8FastCompound (gate8AddedBound 4) 4 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 4 4
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row5 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 5 b =
    (gate8FastCompound (gate8AddedBound 4) 5 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 5 5
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row6 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 6 b =
    (gate8FastCompound (gate8AddedBound 4) 6 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 6 5
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row7 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 7 b =
    (gate8FastCompound (gate8AddedBound 4) 7 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 7 7
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row8 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 8 b =
    (gate8FastCompound (gate8AddedBound 4) 8 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 8 8
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row9 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 9 b =
    (gate8FastCompound (gate8AddedBound 4) 9 b : ℤ) := by
  decide +kernel


end HiddenCircuits.Small
