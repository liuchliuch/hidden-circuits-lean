import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8R1Rows3

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise1_row40 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 40 b =
    (gate8FastCompound (gate8AddedBound 1) 40 b : ℤ) := by
  decide +kernel

theorem gate8_rise1_row41 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 41 b =
    (gate8FastCompound (gate8AddedBound 1) 41 b : ℤ) := by
  decide +kernel

theorem gate8_rise1_row42 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 42 b =
    (gate8FastCompound (gate8AddedBound 1) 42 b : ℤ) := by
  decide +kernel

theorem gate8_rise1_row43 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 43 b =
    (gate8FastCompound (gate8AddedBound 1) 43 b : ℤ) := by
  decide +kernel

theorem gate8_rise1_row44 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 44 b =
    (gate8FastCompound (gate8AddedBound 1) 44 b : ℤ) := by
  decide +kernel

theorem gate8_rise1_row45 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 45 b =
    (gate8FastCompound (gate8AddedBound 1) 45 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 45 45
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row46 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 46 b =
    (gate8FastCompound (gate8AddedBound 1) 46 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 46 46
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row47 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 47 b =
    (gate8FastCompound (gate8AddedBound 1) 47 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 47 47
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row48 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 48 b =
    (gate8FastCompound (gate8AddedBound 1) 48 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 48 48
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row49 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 49 b =
    (gate8FastCompound (gate8AddedBound 1) 49 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 49 49
    (by decide +kernel) (by decide +kernel)

end HiddenCircuits.Small
