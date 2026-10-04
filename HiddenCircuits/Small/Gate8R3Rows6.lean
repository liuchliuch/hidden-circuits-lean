import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8R3Rows5

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise3_row60 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 60 b =
    (gate8FastCompound (gate8AddedBound 3) 60 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 60 60
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row61 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 61 b =
    (gate8FastCompound (gate8AddedBound 3) 61 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 61 58
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row62 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 62 b =
    (gate8FastCompound (gate8AddedBound 3) 62 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 62 59
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row63 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 63 b =
    (gate8FastCompound (gate8AddedBound 3) 63 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 63 60
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row64 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 64 b =
    (gate8FastCompound (gate8AddedBound 3) 64 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 64 64
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row65 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 65 b =
    (gate8FastCompound (gate8AddedBound 3) 65 b : ℤ) := by
  decide +kernel

theorem gate8_rise3_row66 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 66 b =
    (gate8FastCompound (gate8AddedBound 3) 66 b : ℤ) := by
  decide +kernel

theorem gate8_rise3_row67 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 67 b =
    (gate8FastCompound (gate8AddedBound 3) 67 b : ℤ) := by
  decide +kernel

theorem gate8_rise3_row68 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 68 b =
    (gate8FastCompound (gate8AddedBound 3) 68 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 68 68
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise3_row69 : ∀ b, sparseIntProduct Gate8R3ZRows Gate8FNat 69 b =
    (gate8FastCompound (gate8AddedBound 3) 69 b : ℤ) := by
  exact gate8_unit_row Gate8R3ZRows (gate8AddedBound 3) 69 68
    (by decide +kernel) (by decide +kernel)

end HiddenCircuits.Small
