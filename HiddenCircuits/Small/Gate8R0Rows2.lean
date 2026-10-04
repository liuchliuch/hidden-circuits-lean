import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8R0Rows1

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise0_row20 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 20 b =
    (gate8FastCompound (gate8AddedBound 0) 20 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 20 20
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row21 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 21 b =
    (gate8FastCompound (gate8AddedBound 0) 21 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 21 21
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row22 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 22 b =
    (gate8FastCompound (gate8AddedBound 0) 22 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 22 22
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row23 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 23 b =
    (gate8FastCompound (gate8AddedBound 0) 23 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 23 23
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row24 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 24 b =
    (gate8FastCompound (gate8AddedBound 0) 24 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 24 24
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row25 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 25 b =
    (gate8FastCompound (gate8AddedBound 0) 25 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 25 25
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row26 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 26 b =
    (gate8FastCompound (gate8AddedBound 0) 26 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 26 26
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row27 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 27 b =
    (gate8FastCompound (gate8AddedBound 0) 27 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 27 27
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row28 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 28 b =
    (gate8FastCompound (gate8AddedBound 0) 28 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 28 28
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row29 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 29 b =
    (gate8FastCompound (gate8AddedBound 0) 29 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 29 29
    (by decide +kernel) (by decide +kernel)

end HiddenCircuits.Small
