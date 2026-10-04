import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8R3Rows3

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise3_row40 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 40 b =
    (gate8FastCompound (gate8AddedBound 3) 40 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 40 37
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row41 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 41 b =
    (gate8FastCompound (gate8AddedBound 3) 41 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 41 38
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row42 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 42 b =
    (gate8FastCompound (gate8AddedBound 3) 42 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 42 42
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row43 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 43 b =
    (gate8FastCompound (gate8AddedBound 3) 43 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 43 43
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row44 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 44 b =
    (gate8FastCompound (gate8AddedBound 3) 44 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 44 44
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row45 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 45 b =
    (gate8FastCompound (gate8AddedBound 3) 45 b : ℤ) := by
  decide +kernel

theorem gate8_rise3_row46 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 46 b =
    (gate8FastCompound (gate8AddedBound 3) 46 b : ℤ) := by
  decide +kernel

theorem gate8_rise3_row47 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 47 b =
    (gate8FastCompound (gate8AddedBound 3) 47 b : ℤ) := by
  decide +kernel

theorem gate8_rise3_row48 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 48 b =
    (gate8FastCompound (gate8AddedBound 3) 48 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 48 48
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row49 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 49 b =
    (gate8FastCompound (gate8AddedBound 3) 49 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 49 49
    (by decide +kernel) (by decide +kernel)

end HiddenCircuits.Small
