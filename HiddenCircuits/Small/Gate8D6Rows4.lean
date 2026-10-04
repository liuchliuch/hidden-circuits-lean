import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8D6Rows3

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_drop6_row40 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 40 b =
    (gate8FastCompound (gate8DeletedBound 6) 40 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 40 41
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row41 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 41 b =
    (gate8FastCompound (gate8DeletedBound 6) 41 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 41 41
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row42 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 42 b =
    (gate8FastCompound (gate8DeletedBound 6) 42 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 42 43
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row43 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 43 b =
    (gate8FastCompound (gate8DeletedBound 6) 43 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 43 43
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row44 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 44 b =
    (gate8FastCompound (gate8DeletedBound 6) 44 b : ℤ) := by
  decide +kernel

theorem gate8_drop6_row45 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 45 b =
    (gate8FastCompound (gate8DeletedBound 6) 45 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 45 45
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row46 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 46 b =
    (gate8FastCompound (gate8DeletedBound 6) 46 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 46 47
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row47 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 47 b =
    (gate8FastCompound (gate8DeletedBound 6) 47 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 47 47
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row48 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 48 b =
    (gate8FastCompound (gate8DeletedBound 6) 48 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 48 49
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row49 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 49 b =
    (gate8FastCompound (gate8DeletedBound 6) 49 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 49 49
    (by decide +kernel) (by decide +kernel)

end HiddenCircuits.Small
