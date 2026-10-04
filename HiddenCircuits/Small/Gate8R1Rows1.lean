import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8R1Rows0

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise1_row10 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 10 b =
    (gate8FastCompound (gate8AddedBound 1) 10 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 10 10
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row11 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 11 b =
    (gate8FastCompound (gate8AddedBound 1) 11 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 11 11
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row12 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 12 b =
    (gate8FastCompound (gate8AddedBound 1) 12 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 12 12
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row13 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 13 b =
    (gate8FastCompound (gate8AddedBound 1) 13 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 13 13
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row14 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 14 b =
    (gate8FastCompound (gate8AddedBound 1) 14 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 14 14
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row15 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 15 b =
    (gate8FastCompound (gate8AddedBound 1) 15 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 15 5
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row16 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 16 b =
    (gate8FastCompound (gate8AddedBound 1) 16 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 16 6
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row17 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 17 b =
    (gate8FastCompound (gate8AddedBound 1) 17 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 17 7
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row18 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 18 b =
    (gate8FastCompound (gate8AddedBound 1) 18 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 18 8
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row19 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 19 b =
    (gate8FastCompound (gate8AddedBound 1) 19 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 19 9
    (by decide +kernel) (by decide +kernel)

end HiddenCircuits.Small
