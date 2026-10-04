import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8R2Rows2

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise2_row30 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 30 b =
    (gate8FastCompound (gate8AddedBound 2) 30 b : ℤ) := by
  exact gate8_unit_row Gate8R2ZRows (gate8AddedBound 2) 30 24
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise2_row31 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 31 b =
    (gate8FastCompound (gate8AddedBound 2) 31 b : ℤ) := by
  exact gate8_unit_row Gate8R2ZRows (gate8AddedBound 2) 31 31
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise2_row32 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 32 b =
    (gate8FastCompound (gate8AddedBound 2) 32 b : ℤ) := by
  exact gate8_unit_row Gate8R2ZRows (gate8AddedBound 2) 32 32
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise2_row33 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 33 b =
    (gate8FastCompound (gate8AddedBound 2) 33 b : ℤ) := by
  exact gate8_unit_row Gate8R2ZRows (gate8AddedBound 2) 33 33
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise2_row34 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 34 b =
    (gate8FastCompound (gate8AddedBound 2) 34 b : ℤ) := by
  exact gate8_unit_row Gate8R2ZRows (gate8AddedBound 2) 34 34
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise2_row35 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 35 b =
    (gate8FastCompound (gate8AddedBound 2) 35 b : ℤ) := by
  decide +kernel

theorem gate8_rise2_row36 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 36 b =
    (gate8FastCompound (gate8AddedBound 2) 36 b : ℤ) := by
  decide +kernel

theorem gate8_rise2_row37 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 37 b =
    (gate8FastCompound (gate8AddedBound 2) 37 b : ℤ) := by
  decide +kernel

theorem gate8_rise2_row38 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 38 b =
    (gate8FastCompound (gate8AddedBound 2) 38 b : ℤ) := by
  decide +kernel

theorem gate8_rise2_row39 : ∀ b, sparseIntProduct Gate8R2ZRows Gate8FNat 39 b =
    (gate8FastCompound (gate8AddedBound 2) 39 b : ℤ) := by
  exact gate8_unit_row Gate8R2ZRows (gate8AddedBound 2) 39 39
    (by decide +kernel) (by decide +kernel)

end HiddenCircuits.Small
