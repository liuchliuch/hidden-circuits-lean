import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8R1Rows5

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise1_row60 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 60 b =
    (gate8FastCompound (gate8AddedBound 1) 60 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 60 50
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row61 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 61 b =
    (gate8FastCompound (gate8AddedBound 1) 61 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 61 51
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row62 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 62 b =
    (gate8FastCompound (gate8AddedBound 1) 62 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 62 52
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row63 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 63 b =
    (gate8FastCompound (gate8AddedBound 1) 63 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 63 53
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row64 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 64 b =
    (gate8FastCompound (gate8AddedBound 1) 64 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 64 54
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row65 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 65 b =
    (gate8FastCompound (gate8AddedBound 1) 65 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 65 65
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row66 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 66 b =
    (gate8FastCompound (gate8AddedBound 1) 66 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 66 66
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row67 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 67 b =
    (gate8FastCompound (gate8AddedBound 1) 67 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 67 67
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row68 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 68 b =
    (gate8FastCompound (gate8AddedBound 1) 68 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 68 68
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row69 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 69 b =
    (gate8FastCompound (gate8AddedBound 1) 69 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 69 69
    (by decide +kernel) (by decide +kernel)

end HiddenCircuits.Small
