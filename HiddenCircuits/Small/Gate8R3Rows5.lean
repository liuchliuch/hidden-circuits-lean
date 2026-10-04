import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8R3Rows4

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise3_row50 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 50 b =
    (gate8FastCompound (gate8AddedBound 3) 50 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 50 50
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row51 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 51 b =
    (gate8FastCompound (gate8AddedBound 3) 51 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 51 48
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row52 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 52 b =
    (gate8FastCompound (gate8AddedBound 3) 52 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 52 49
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row53 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 53 b =
    (gate8FastCompound (gate8AddedBound 3) 53 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 53 50
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row54 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 54 b =
    (gate8FastCompound (gate8AddedBound 3) 54 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 54 54
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row55 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 55 b =
    (gate8FastCompound (gate8AddedBound 3) 55 b : ℤ) := by
  decide +kernel

theorem gate8_rise3_row56 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 56 b =
    (gate8FastCompound (gate8AddedBound 3) 56 b : ℤ) := by
  decide +kernel

theorem gate8_rise3_row57 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 57 b =
    (gate8FastCompound (gate8AddedBound 3) 57 b : ℤ) := by
  decide +kernel

theorem gate8_rise3_row58 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 58 b =
    (gate8FastCompound (gate8AddedBound 3) 58 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 58 58
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row59 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 59 b =
    (gate8FastCompound (gate8AddedBound 3) 59 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 59 59
    (by decide +kernel) (by decide +kernel)

end HiddenCircuits.Small
