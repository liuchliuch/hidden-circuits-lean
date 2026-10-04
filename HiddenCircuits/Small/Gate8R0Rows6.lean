import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8R0Rows5

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise0_row60 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 60 b =
    (gate8FastCompound (gate8AddedBound 0) 60 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 60 60
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row61 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 61 b =
    (gate8FastCompound (gate8AddedBound 0) 61 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 61 61
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row62 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 62 b =
    (gate8FastCompound (gate8AddedBound 0) 62 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 62 62
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row63 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 63 b =
    (gate8FastCompound (gate8AddedBound 0) 63 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 63 63
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row64 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 64 b =
    (gate8FastCompound (gate8AddedBound 0) 64 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 64 64
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row65 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 65 b =
    (gate8FastCompound (gate8AddedBound 0) 65 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 65 65
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row66 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 66 b =
    (gate8FastCompound (gate8AddedBound 0) 66 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 66 66
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row67 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 67 b =
    (gate8FastCompound (gate8AddedBound 0) 67 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 67 67
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row68 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 68 b =
    (gate8FastCompound (gate8AddedBound 0) 68 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 68 68
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row69 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 69 b =
    (gate8FastCompound (gate8AddedBound 0) 69 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 69 69
    (by decide +kernel) (by decide +kernel)

end HiddenCircuits.Small
