import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8R3Rows1

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise3_row20 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 20 b =
    (gate8FastCompound (gate8AddedBound 3) 20 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 20 17
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row21 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 21 b =
    (gate8FastCompound (gate8AddedBound 3) 21 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 21 18
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row22 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 22 b =
    (gate8FastCompound (gate8AddedBound 3) 22 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 22 22
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row23 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 23 b =
    (gate8FastCompound (gate8AddedBound 3) 23 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 23 23
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row24 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 24 b =
    (gate8FastCompound (gate8AddedBound 3) 24 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 24 24
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row25 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 25 b =
    (gate8FastCompound (gate8AddedBound 3) 25 b : ℤ) := by
  decide +kernel

theorem gate8_rise3_row26 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 26 b =
    (gate8FastCompound (gate8AddedBound 3) 26 b : ℤ) := by
  decide +kernel

theorem gate8_rise3_row27 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 27 b =
    (gate8FastCompound (gate8AddedBound 3) 27 b : ℤ) := by
  decide +kernel

theorem gate8_rise3_row28 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 28 b =
    (gate8FastCompound (gate8AddedBound 3) 28 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 28 28
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row29 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 29 b =
    (gate8FastCompound (gate8AddedBound 3) 29 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 29 29
    (by decide +kernel) (by decide +kernel)

end HiddenCircuits.Small
