import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8R3Rows2

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise3_row30 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 30 b =
    (gate8FastCompound (gate8AddedBound 3) 30 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 30 30
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row31 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 31 b =
    (gate8FastCompound (gate8AddedBound 3) 31 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 31 28
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row32 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 32 b =
    (gate8FastCompound (gate8AddedBound 3) 32 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 32 29
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row33 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 33 b =
    (gate8FastCompound (gate8AddedBound 3) 33 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 33 30
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row34 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 34 b =
    (gate8FastCompound (gate8AddedBound 3) 34 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 34 34
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row35 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 35 b =
    (gate8FastCompound (gate8AddedBound 3) 35 b : ℤ) := by
  decide +kernel

theorem gate8_rise3_row36 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 36 b =
    (gate8FastCompound (gate8AddedBound 3) 36 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 36 36
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row37 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 37 b =
    (gate8FastCompound (gate8AddedBound 3) 37 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 37 37
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row38 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 38 b =
    (gate8FastCompound (gate8AddedBound 3) 38 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 38 38
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row39 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 39 b =
    (gate8FastCompound (gate8AddedBound 3) 39 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 39 36
    (by decide +kernel) (by decide +kernel)

end HiddenCircuits.Small
