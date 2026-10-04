import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8R0Rows4

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise0_row50 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 50 b =
    (gate8FastCompound (gate8AddedBound 0) 50 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 50 30
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row51 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 51 b =
    (gate8FastCompound (gate8AddedBound 0) 51 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 51 31
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row52 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 52 b =
    (gate8FastCompound (gate8AddedBound 0) 52 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 52 32
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row53 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 53 b =
    (gate8FastCompound (gate8AddedBound 0) 53 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 53 33
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row54 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 54 b =
    (gate8FastCompound (gate8AddedBound 0) 54 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 54 34
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row55 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 55 b =
    (gate8FastCompound (gate8AddedBound 0) 55 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 55 55
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row56 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 56 b =
    (gate8FastCompound (gate8AddedBound 0) 56 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 56 56
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row57 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 57 b =
    (gate8FastCompound (gate8AddedBound 0) 57 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 57 57
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row58 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 58 b =
    (gate8FastCompound (gate8AddedBound 0) 58 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 58 58
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row59 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 59 b =
    (gate8FastCompound (gate8AddedBound 0) 59 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 59 59
    (by decide +kernel) (by decide +kernel)

end HiddenCircuits.Small
