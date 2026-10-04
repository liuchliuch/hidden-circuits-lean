import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8R4Rows4

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise4_row50 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 50 b =
    (gate8FastCompound (gate8AddedBound 4) 50 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 50 50
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row51 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 51 b =
    (gate8FastCompound (gate8AddedBound 4) 51 b : ℤ) := by
  decide +kernel

theorem gate8_rise4_row52 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 52 b =
    (gate8FastCompound (gate8AddedBound 4) 52 b : ℤ) := by
  decide +kernel

theorem gate8_rise4_row53 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 53 b =
    (gate8FastCompound (gate8AddedBound 4) 53 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 53 53
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row54 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 54 b =
    (gate8FastCompound (gate8AddedBound 4) 54 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 54 53
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row55 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 55 b =
    (gate8FastCompound (gate8AddedBound 4) 55 b : ℤ) := by
  decide +kernel

theorem gate8_rise4_row56 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 56 b =
    (gate8FastCompound (gate8AddedBound 4) 56 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 56 56
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row57 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 57 b =
    (gate8FastCompound (gate8AddedBound 4) 57 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 57 57
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row58 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 58 b =
    (gate8FastCompound (gate8AddedBound 4) 58 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 58 56
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row59 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 59 b =
    (gate8FastCompound (gate8AddedBound 4) 59 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 59 57
    (by decide +kernel) (by decide +kernel)

end HiddenCircuits.Small
