import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8D2Rows0

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_drop2_row10 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 10 b =
    (gate8FastCompound (gate8DeletedBound 2) 10 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 10 10
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop2_row11 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 11 b =
    (gate8FastCompound (gate8DeletedBound 2) 11 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 11 11
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop2_row12 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 12 b =
    (gate8FastCompound (gate8DeletedBound 2) 12 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 12 12
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop2_row13 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 13 b =
    (gate8FastCompound (gate8DeletedBound 2) 13 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 13 13
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop2_row14 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 14 b =
    (gate8FastCompound (gate8DeletedBound 2) 14 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 14 14
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop2_row15 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 15 b =
    (gate8FastCompound (gate8DeletedBound 2) 15 b : ℤ) := by
  decide +kernel

theorem gate8_drop2_row16 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 16 b =
    (gate8FastCompound (gate8DeletedBound 2) 16 b : ℤ) := by
  decide +kernel

theorem gate8_drop2_row17 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 17 b =
    (gate8FastCompound (gate8DeletedBound 2) 17 b : ℤ) := by
  decide +kernel

theorem gate8_drop2_row18 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 18 b =
    (gate8FastCompound (gate8DeletedBound 2) 18 b : ℤ) := by
  decide +kernel

theorem gate8_drop2_row19 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 19 b =
    (gate8FastCompound (gate8DeletedBound 2) 19 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 19 25
    (by decide +kernel) (by decide +kernel)

end HiddenCircuits.Small
