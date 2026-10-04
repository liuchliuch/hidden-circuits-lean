import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8D6Rows5

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_drop6_row60 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 60 b =
    (gate8FastCompound (gate8DeletedBound 6) 60 b : ℤ) := by
  decide +kernel

theorem gate8_drop6_row61 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 61 b =
    (gate8FastCompound (gate8DeletedBound 6) 61 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 61 62
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row62 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 62 b =
    (gate8FastCompound (gate8DeletedBound 6) 62 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 62 62
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row63 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 63 b =
    (gate8FastCompound (gate8DeletedBound 6) 63 b : ℤ) := by
  decide +kernel

theorem gate8_drop6_row64 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 64 b =
    (gate8FastCompound (gate8DeletedBound 6) 64 b : ℤ) := by
  decide +kernel

theorem gate8_drop6_row65 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 65 b =
    (gate8FastCompound (gate8DeletedBound 6) 65 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 65 66
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row66 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 66 b =
    (gate8FastCompound (gate8DeletedBound 6) 66 b : ℤ) := by
  exact gate8_unit_row Gate8D6ZRows (gate8DeletedBound 6) 66 66
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop6_row67 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 67 b =
    (gate8FastCompound (gate8DeletedBound 6) 67 b : ℤ) := by
  decide +kernel

theorem gate8_drop6_row68 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 68 b =
    (gate8FastCompound (gate8DeletedBound 6) 68 b : ℤ) := by
  decide +kernel

theorem gate8_drop6_row69 : ∀ b, sparseIntProduct Gate8D6ZRows Gate8FNat 69 b =
    (gate8FastCompound (gate8DeletedBound 6) 69 b : ℤ) := by
  decide +kernel


end HiddenCircuits.Small
