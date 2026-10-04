import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8R2Rows3

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise2_row40 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 40 b =
    (gate8FastCompound (gate8AddedBound 2) 40 b : ℤ) := by
  exact gate8_unit_row Gate8R2ZRows (gate8AddedBound 2) 40 40
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise2_row41 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 41 b =
    (gate8FastCompound (gate8AddedBound 2) 41 b : ℤ) := by
  exact gate8_unit_row Gate8R2ZRows (gate8AddedBound 2) 41 41
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise2_row42 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 42 b =
    (gate8FastCompound (gate8AddedBound 2) 42 b : ℤ) := by
  exact gate8_unit_row Gate8R2ZRows (gate8AddedBound 2) 42 42
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise2_row43 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 43 b =
    (gate8FastCompound (gate8AddedBound 2) 43 b : ℤ) := by
  exact gate8_unit_row Gate8R2ZRows (gate8AddedBound 2) 43 43
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise2_row44 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 44 b =
    (gate8FastCompound (gate8AddedBound 2) 44 b : ℤ) := by
  exact gate8_unit_row Gate8R2ZRows (gate8AddedBound 2) 44 44
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise2_row45 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 45 b =
    (gate8FastCompound (gate8AddedBound 2) 45 b : ℤ) := by
  exact gate8_unit_row Gate8R2ZRows (gate8AddedBound 2) 45 39
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise2_row46 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 46 b =
    (gate8FastCompound (gate8AddedBound 2) 46 b : ℤ) := by
  exact gate8_unit_row Gate8R2ZRows (gate8AddedBound 2) 46 40
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise2_row47 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 47 b =
    (gate8FastCompound (gate8AddedBound 2) 47 b : ℤ) := by
  exact gate8_unit_row Gate8R2ZRows (gate8AddedBound 2) 47 41
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise2_row48 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 48 b =
    (gate8FastCompound (gate8AddedBound 2) 48 b : ℤ) := by
  exact gate8_unit_row Gate8R2ZRows (gate8AddedBound 2) 48 42
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise2_row49 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 49 b =
    (gate8FastCompound (gate8AddedBound 2) 49 b : ℤ) := by
  exact gate8_unit_row Gate8R2ZRows (gate8AddedBound 2) 49 43
    (by decide +kernel) (by decide +kernel)

end HiddenCircuits.Small
