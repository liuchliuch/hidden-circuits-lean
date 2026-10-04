import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8R3Rows0

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise3_row10 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 10 b =
    (gate8FastCompound (gate8AddedBound 3) 10 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 10 7
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row11 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 11 b =
    (gate8FastCompound (gate8AddedBound 3) 11 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 11 8
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row12 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 12 b =
    (gate8FastCompound (gate8AddedBound 3) 12 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 12 12
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row13 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 13 b =
    (gate8FastCompound (gate8AddedBound 3) 13 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 13 13
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row14 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 14 b =
    (gate8FastCompound (gate8AddedBound 3) 14 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 14 14
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row15 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 15 b =
    (gate8FastCompound (gate8AddedBound 3) 15 b : ℤ) := by
  decide +kernel

theorem gate8_rise3_row16 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 16 b =
    (gate8FastCompound (gate8AddedBound 3) 16 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 16 16
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row17 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 17 b =
    (gate8FastCompound (gate8AddedBound 3) 17 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 17 17
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row18 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 18 b =
    (gate8FastCompound (gate8AddedBound 3) 18 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 18 18
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row19 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 19 b =
    (gate8FastCompound (gate8AddedBound 3) 19 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 19 16
    (by decide +kernel) (by decide +kernel)

end HiddenCircuits.Small
