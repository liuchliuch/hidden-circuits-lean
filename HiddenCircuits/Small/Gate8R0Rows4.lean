import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8R0Rows3

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise0_row40 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 40 b =
    (gate8FastCompound (gate8AddedBound 0) 40 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 40 20
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row41 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 41 b =
    (gate8FastCompound (gate8AddedBound 0) 41 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 41 21
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row42 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 42 b =
    (gate8FastCompound (gate8AddedBound 0) 42 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 42 22
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row43 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 43 b =
    (gate8FastCompound (gate8AddedBound 0) 43 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 43 23
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row44 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 44 b =
    (gate8FastCompound (gate8AddedBound 0) 44 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 44 24
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row45 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 45 b =
    (gate8FastCompound (gate8AddedBound 0) 45 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 45 25
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row46 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 46 b =
    (gate8FastCompound (gate8AddedBound 0) 46 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 46 26
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row47 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 47 b =
    (gate8FastCompound (gate8AddedBound 0) 47 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 47 27
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row48 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 48 b =
    (gate8FastCompound (gate8AddedBound 0) 48 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 48 28
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise0_row49 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 49 b =
    (gate8FastCompound (gate8AddedBound 0) 49 b : ℤ) := by
  exact gate8_unit_row Gate8R0ZRows (gate8AddedBound 0) 49 29
    (by decide +kernel) (by decide +kernel)

end HiddenCircuits.Small
