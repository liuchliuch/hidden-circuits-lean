import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8D6Rows4

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_drop6_row50 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 50 b =
    (gate8FastCompound (gate8DeletedBound 6) 50 b : ℤ) := by
  decide +kernel

theorem gate8_drop6_row51 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 51 b =
    (gate8FastCompound (gate8DeletedBound 6) 51 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 51 52
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row52 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 52 b =
    (gate8FastCompound (gate8DeletedBound 6) 52 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 52 52
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row53 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 53 b =
    (gate8FastCompound (gate8DeletedBound 6) 53 b : ℤ) := by
  decide +kernel

theorem gate8_drop6_row54 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 54 b =
    (gate8FastCompound (gate8DeletedBound 6) 54 b : ℤ) := by
  decide +kernel

theorem gate8_drop6_row55 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 55 b =
    (gate8FastCompound (gate8DeletedBound 6) 55 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 55 55
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row56 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 56 b =
    (gate8FastCompound (gate8DeletedBound 6) 56 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 56 57
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row57 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 57 b =
    (gate8FastCompound (gate8DeletedBound 6) 57 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 57 57
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row58 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 58 b =
    (gate8FastCompound (gate8DeletedBound 6) 58 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 58 59
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row59 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 59 b =
    (gate8FastCompound (gate8DeletedBound 6) 59 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 59 59
    (by decide +kernel) (by decide +kernel)

end HiddenCircuits.Small
