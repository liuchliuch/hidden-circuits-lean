import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8R1Rows1

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise1_row20 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 20 b =
    (gate8FastCompound (gate8AddedBound 1) 20 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 20 10
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row21 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 21 b =
    (gate8FastCompound (gate8AddedBound 1) 21 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 21 11
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row22 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 22 b =
    (gate8FastCompound (gate8AddedBound 1) 22 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 22 12
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row23 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 23 b =
    (gate8FastCompound (gate8AddedBound 1) 23 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 23 13
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row24 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 24 b =
    (gate8FastCompound (gate8AddedBound 1) 24 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 24 14
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row25 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 25 b =
    (gate8FastCompound (gate8AddedBound 1) 25 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 25 25
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row26 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 26 b =
    (gate8FastCompound (gate8AddedBound 1) 26 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 26 26
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row27 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 27 b =
    (gate8FastCompound (gate8AddedBound 1) 27 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 27 27
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row28 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 28 b =
    (gate8FastCompound (gate8AddedBound 1) 28 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 28 28
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row29 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 29 b =
    (gate8FastCompound (gate8AddedBound 1) 29 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 29 29
    (by decide +kernel) (by decide +kernel)

end HiddenCircuits.Small
