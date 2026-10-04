import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8D2Rows1

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_drop2_row20 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 20 b =
    (gate8FastCompound (gate8DeletedBound 2) 20 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 20 26
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop2_row21 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 21 b =
    (gate8FastCompound (gate8DeletedBound 2) 21 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 21 27
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop2_row22 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 22 b =
    (gate8FastCompound (gate8DeletedBound 2) 22 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 22 28
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop2_row23 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 23 b =
    (gate8FastCompound (gate8DeletedBound 2) 23 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 23 29
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop2_row24 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 24 b =
    (gate8FastCompound (gate8DeletedBound 2) 24 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 24 30
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop2_row25 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 25 b =
    (gate8FastCompound (gate8DeletedBound 2) 25 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 25 25
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop2_row26 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 26 b =
    (gate8FastCompound (gate8DeletedBound 2) 26 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 26 26
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop2_row27 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 27 b =
    (gate8FastCompound (gate8DeletedBound 2) 27 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 27 27
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop2_row28 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 28 b =
    (gate8FastCompound (gate8DeletedBound 2) 28 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 28 28
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop2_row29 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 29 b =
    (gate8FastCompound (gate8DeletedBound 2) 29 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 29 29
    (by decide +kernel) (by decide +kernel)

end HiddenCircuits.Small
