import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8R4Rows3

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise4_row40 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 40 b =
    (gate8FastCompound (gate8AddedBound 4) 40 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 40 40
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row41 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 41 b =
    (gate8FastCompound (gate8AddedBound 4) 41 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 41 41
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row42 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 42 b =
    (gate8FastCompound (gate8AddedBound 4) 42 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 42 40
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row43 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 43 b =
    (gate8FastCompound (gate8AddedBound 4) 43 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 43 41
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row44 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 44 b =
    (gate8FastCompound (gate8AddedBound 4) 44 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 44 44
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row45 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 45 b =
    (gate8FastCompound (gate8AddedBound 4) 45 b : ℤ) := by
  decide +kernel

theorem gate8_rise4_row46 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 46 b =
    (gate8FastCompound (gate8AddedBound 4) 46 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 46 46
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row47 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 47 b =
    (gate8FastCompound (gate8AddedBound 4) 47 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 47 47
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row48 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 48 b =
    (gate8FastCompound (gate8AddedBound 4) 48 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 48 46
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row49 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 49 b =
    (gate8FastCompound (gate8AddedBound 4) 49 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 49 47
    (by decide +kernel) (by decide +kernel)

end HiddenCircuits.Small
