import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8R0Rows0

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise0_row10 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 10 b =
    (gate8FastCompound (gate8AddedBound 0) 10 b : ℤ) := by
  decide +kernel

theorem gate8_rise0_row11 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 11 b =
    (gate8FastCompound (gate8AddedBound 0) 11 b : ℤ) := by
  decide +kernel

theorem gate8_rise0_row12 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 12 b =
    (gate8FastCompound (gate8AddedBound 0) 12 b : ℤ) := by
  decide +kernel

theorem gate8_rise0_row13 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 13 b =
    (gate8FastCompound (gate8AddedBound 0) 13 b : ℤ) := by
  decide +kernel

theorem gate8_rise0_row14 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 14 b =
    (gate8FastCompound (gate8AddedBound 0) 14 b : ℤ) := by
  decide +kernel

theorem gate8_rise0_row15 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 15 b =
    (gate8FastCompound (gate8AddedBound 0) 15 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 15 15
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row16 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 16 b =
    (gate8FastCompound (gate8AddedBound 0) 16 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 16 16
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row17 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 17 b =
    (gate8FastCompound (gate8AddedBound 0) 17 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 17 17
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row18 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 18 b =
    (gate8FastCompound (gate8AddedBound 0) 18 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 18 18
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row19 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 19 b =
    (gate8FastCompound (gate8AddedBound 0) 19 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 19 19
    (by decide +kernel) (by decide +kernel)

end HiddenCircuits.Small
