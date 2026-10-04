import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8D2Rows3

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_drop2_row40 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 40 b =
    (gate8FastCompound (gate8DeletedBound 2) 40 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 40 46
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop2_row41 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 41 b =
    (gate8FastCompound (gate8DeletedBound 2) 41 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 41 47
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop2_row42 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 42 b =
    (gate8FastCompound (gate8DeletedBound 2) 42 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 42 48
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop2_row43 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 43 b =
    (gate8FastCompound (gate8DeletedBound 2) 43 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 43 49
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop2_row44 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 44 b =
    (gate8FastCompound (gate8DeletedBound 2) 44 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 44 50
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop2_row45 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 45 b =
    (gate8FastCompound (gate8DeletedBound 2) 45 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 45 45
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop2_row46 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 46 b =
    (gate8FastCompound (gate8DeletedBound 2) 46 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 46 46
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop2_row47 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 47 b =
    (gate8FastCompound (gate8DeletedBound 2) 47 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 47 47
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop2_row48 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 48 b =
    (gate8FastCompound (gate8DeletedBound 2) 48 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 48 48
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop2_row49 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 49 b =
    (gate8FastCompound (gate8DeletedBound 2) 49 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 49 49
    (by decide +kernel) (by decide +kernel)

end HiddenCircuits.Small
