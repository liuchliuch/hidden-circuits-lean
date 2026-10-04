import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8R0Rows2

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise0_row30 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 30 b =
    (gate8FastCompound (gate8AddedBound 0) 30 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 30 30
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row31 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 31 b =
    (gate8FastCompound (gate8AddedBound 0) 31 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 31 31
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row32 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 32 b =
    (gate8FastCompound (gate8AddedBound 0) 32 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 32 32
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row33 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 33 b =
    (gate8FastCompound (gate8AddedBound 0) 33 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 33 33
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row34 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 34 b =
    (gate8FastCompound (gate8AddedBound 0) 34 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 34 34
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row35 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 35 b =
    (gate8FastCompound (gate8AddedBound 0) 35 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 35 15
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row36 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 36 b =
    (gate8FastCompound (gate8AddedBound 0) 36 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 36 16
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row37 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 37 b =
    (gate8FastCompound (gate8AddedBound 0) 37 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 37 17
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row38 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 38 b =
    (gate8FastCompound (gate8AddedBound 0) 38 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 38 18
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row39 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 39 b =
    (gate8FastCompound (gate8AddedBound 0) 39 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 39 19
    (by decide +kernel) (by decide +kernel)

end HiddenCircuits.Small
