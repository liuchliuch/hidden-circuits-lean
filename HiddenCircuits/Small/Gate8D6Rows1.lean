import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8D6Rows0

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_drop6_row10 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 10 b =
    (gate8FastCompound (gate8DeletedBound 6) 10 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 10 11
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row11 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 11 b =
    (gate8FastCompound (gate8DeletedBound 6) 11 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 11 11
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row12 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 12 b =
    (gate8FastCompound (gate8DeletedBound 6) 12 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 12 13
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row13 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 13 b =
    (gate8FastCompound (gate8DeletedBound 6) 13 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 13 13
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row14 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 14 b =
    (gate8FastCompound (gate8DeletedBound 6) 14 b : ℤ) := by
  decide +kernel

theorem gate8_drop6_row15 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 15 b =
    (gate8FastCompound (gate8DeletedBound 6) 15 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 15 15
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row16 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 16 b =
    (gate8FastCompound (gate8DeletedBound 6) 16 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 16 16
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row17 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 17 b =
    (gate8FastCompound (gate8DeletedBound 6) 17 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 17 18
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row18 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 18 b =
    (gate8FastCompound (gate8DeletedBound 6) 18 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 18 18
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row19 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 19 b =
    (gate8FastCompound (gate8DeletedBound 6) 19 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 19 19
    (by decide +kernel) (by decide +kernel)

end HiddenCircuits.Small
