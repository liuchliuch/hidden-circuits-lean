import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8D2Rows4

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_drop2_row50 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 50 b =
    (gate8FastCompound (gate8DeletedBound 2) 50 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 50 50
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop2_row51 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 51 b =
    (gate8FastCompound (gate8DeletedBound 2) 51 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 51 51
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop2_row52 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 52 b =
    (gate8FastCompound (gate8DeletedBound 2) 52 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 52 52
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop2_row53 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 53 b =
    (gate8FastCompound (gate8DeletedBound 2) 53 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 53 53
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop2_row54 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 54 b =
    (gate8FastCompound (gate8DeletedBound 2) 54 b : ℤ) := by
  exact gate8_unit_row Gate8D2ZRows (gate8DeletedBound 2) 54 54
    (by decide +kernel) (by decide +kernel)

theorem gate8_drop2_row55 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 55 b =
    (gate8FastCompound (gate8DeletedBound 2) 55 b : ℤ) := by
  decide +kernel

theorem gate8_drop2_row56 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 56 b =
    (gate8FastCompound (gate8DeletedBound 2) 56 b : ℤ) := by
  decide +kernel

theorem gate8_drop2_row57 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 57 b =
    (gate8FastCompound (gate8DeletedBound 2) 57 b : ℤ) := by
  decide +kernel

theorem gate8_drop2_row58 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 58 b =
    (gate8FastCompound (gate8DeletedBound 2) 58 b : ℤ) := by
  decide +kernel

theorem gate8_drop2_row59 : ∀ b, sparseIntProduct Gate8D2ZRows Gate8FNat 59 b =
    (gate8FastCompound (gate8DeletedBound 2) 59 b : ℤ) := by
  decide +kernel


end HiddenCircuits.Small
