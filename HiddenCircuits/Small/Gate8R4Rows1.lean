import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8R4Rows0

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise4_row10 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 10 b =
    (gate8FastCompound (gate8AddedBound 4) 10 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 10 10
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row11 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 11 b =
    (gate8FastCompound (gate8AddedBound 4) 11 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 11 11
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row12 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 12 b =
    (gate8FastCompound (gate8AddedBound 4) 12 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 12 10
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row13 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 13 b =
    (gate8FastCompound (gate8AddedBound 4) 13 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 13 11
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row14 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 14 b =
    (gate8FastCompound (gate8AddedBound 4) 14 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 14 14
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row15 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 15 b =
    (gate8FastCompound (gate8AddedBound 4) 15 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 15 15
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row16 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 16 b =
    (gate8FastCompound (gate8AddedBound 4) 16 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 16 15
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row17 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 17 b =
    (gate8FastCompound (gate8AddedBound 4) 17 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 17 17
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row18 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 18 b =
    (gate8FastCompound (gate8AddedBound 4) 18 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 18 18
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row19 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 19 b =
    (gate8FastCompound (gate8AddedBound 4) 19 b : ℤ) := by
  decide +kernel


end HiddenCircuits.Small
