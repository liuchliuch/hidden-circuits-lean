import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8D2Rows5

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_drop2_row60 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 60 b =
    (gate8FastCompound (gate8DeletedBound 2) 60 b : ℤ) := by
  decide +kernel

theorem gate8_drop2_row61 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 61 b =
    (gate8FastCompound (gate8DeletedBound 2) 61 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 61 65
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop2_row62 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 62 b =
    (gate8FastCompound (gate8DeletedBound 2) 62 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 62 66
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop2_row63 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 63 b =
    (gate8FastCompound (gate8DeletedBound 2) 63 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 63 67
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop2_row64 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 64 b =
    (gate8FastCompound (gate8DeletedBound 2) 64 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 64 68
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop2_row65 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 65 b =
    (gate8FastCompound (gate8DeletedBound 2) 65 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 65 65
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop2_row66 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 66 b =
    (gate8FastCompound (gate8DeletedBound 2) 66 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 66 66
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop2_row67 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 67 b =
    (gate8FastCompound (gate8DeletedBound 2) 67 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 67 67
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop2_row68 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 68 b =
    (gate8FastCompound (gate8DeletedBound 2) 68 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 68 68
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop2_row69 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 69 b =
    (gate8FastCompound (gate8DeletedBound 2) 69 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 69 69
    (by decide +kernel) (by decide +kernel)

end HiddenCircuits.Small
