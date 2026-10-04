import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8R2Rows5

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise2_row60 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 60 b =
    (gate8FastCompound (gate8AddedBound 2) 60 b : ℤ) := by
  decide +kernel

theorem gate8_rise2_row61 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 61 b =
    (gate8FastCompound (gate8AddedBound 2) 61 b : ℤ) := by
  exact gate8_unit_row Gate8R2ZRows (gate8AddedBound 2) 61 61
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise2_row62 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 62 b =
    (gate8FastCompound (gate8AddedBound 2) 62 b : ℤ) := by
  exact gate8_unit_row Gate8R2ZRows (gate8AddedBound 2) 62 62
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise2_row63 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 63 b =
    (gate8FastCompound (gate8AddedBound 2) 63 b : ℤ) := by
  exact gate8_unit_row Gate8R2ZRows (gate8AddedBound 2) 63 63
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise2_row64 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 64 b =
    (gate8FastCompound (gate8AddedBound 2) 64 b : ℤ) := by
  exact gate8_unit_row Gate8R2ZRows (gate8AddedBound 2) 64 64
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise2_row65 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 65 b =
    (gate8FastCompound (gate8AddedBound 2) 65 b : ℤ) := by
  exact gate8_unit_row Gate8R2ZRows (gate8AddedBound 2) 65 61
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise2_row66 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 66 b =
    (gate8FastCompound (gate8AddedBound 2) 66 b : ℤ) := by
  exact gate8_unit_row Gate8R2ZRows (gate8AddedBound 2) 66 62
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise2_row67 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 67 b =
    (gate8FastCompound (gate8AddedBound 2) 67 b : ℤ) := by
  exact gate8_unit_row Gate8R2ZRows (gate8AddedBound 2) 67 63
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise2_row68 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 68 b =
    (gate8FastCompound (gate8AddedBound 2) 68 b : ℤ) := by
  exact gate8_unit_row Gate8R2ZRows (gate8AddedBound 2) 68 64
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise2_row69 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 69 b =
    (gate8FastCompound (gate8AddedBound 2) 69 b : ℤ) := by
  exact gate8_unit_row Gate8R2ZRows (gate8AddedBound 2) 69 69
    (by decide +kernel) (by decide +kernel)

end HiddenCircuits.Small
