import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8D6Rows1

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_drop6_row20 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 20 b =
    (gate8FastCompound (gate8DeletedBound 6) 20 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 20 21
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row21 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 21 b =
    (gate8FastCompound (gate8DeletedBound 6) 21 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 21 21
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row22 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 22 b =
    (gate8FastCompound (gate8DeletedBound 6) 22 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 22 23
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row23 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 23 b =
    (gate8FastCompound (gate8DeletedBound 6) 23 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 23 23
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row24 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 24 b =
    (gate8FastCompound (gate8DeletedBound 6) 24 b : ℤ) := by
  decide +kernel

theorem gate8_drop6_row25 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 25 b =
    (gate8FastCompound (gate8DeletedBound 6) 25 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 25 25
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row26 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 26 b =
    (gate8FastCompound (gate8DeletedBound 6) 26 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 26 27
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row27 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 27 b =
    (gate8FastCompound (gate8DeletedBound 6) 27 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 27 27
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row28 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 28 b =
    (gate8FastCompound (gate8DeletedBound 6) 28 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 28 29
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row29 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 29 b =
    (gate8FastCompound (gate8DeletedBound 6) 29 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 29 29
    (by decide +kernel) (by decide +kernel)

end HiddenCircuits.Small
