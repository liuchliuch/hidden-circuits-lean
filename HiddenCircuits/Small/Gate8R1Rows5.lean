import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8R1Rows4

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise1_row50 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 50 b =
    (gate8FastCompound (gate8AddedBound 1) 50 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 50 50
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row51 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 51 b =
    (gate8FastCompound (gate8AddedBound 1) 51 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 51 51
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row52 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 52 b =
    (gate8FastCompound (gate8AddedBound 1) 52 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 52 52
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row53 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 53 b =
    (gate8FastCompound (gate8AddedBound 1) 53 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 53 53
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row54 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 54 b =
    (gate8FastCompound (gate8AddedBound 1) 54 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 54 54
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row55 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 55 b =
    (gate8FastCompound (gate8AddedBound 1) 55 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 55 45
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row56 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 56 b =
    (gate8FastCompound (gate8AddedBound 1) 56 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 56 46
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row57 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 57 b =
    (gate8FastCompound (gate8AddedBound 1) 57 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 57 47
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row58 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 58 b =
    (gate8FastCompound (gate8AddedBound 1) 58 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 58 48
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row59 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 59 b =
    (gate8FastCompound (gate8AddedBound 1) 59 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 59 49
    (by decide +kernel) (by decide +kernel)

end HiddenCircuits.Small
