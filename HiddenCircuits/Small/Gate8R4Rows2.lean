import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8R4Rows1

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise4_row20 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 20 b =
    (gate8FastCompound (gate8AddedBound 4) 20 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 20 20
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row21 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 21 b =
    (gate8FastCompound (gate8AddedBound 4) 21 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 21 21
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row22 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 22 b =
    (gate8FastCompound (gate8AddedBound 4) 22 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 22 20
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row23 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 23 b =
    (gate8FastCompound (gate8AddedBound 4) 23 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 23 21
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row24 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 24 b =
    (gate8FastCompound (gate8AddedBound 4) 24 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 24 24
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row25 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 25 b =
    (gate8FastCompound (gate8AddedBound 4) 25 b : ℤ) := by
  decide +kernel

theorem gate8_rise4_row26 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 26 b =
    (gate8FastCompound (gate8AddedBound 4) 26 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 26 26
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row27 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 27 b =
    (gate8FastCompound (gate8AddedBound 4) 27 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 27 27
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row28 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 28 b =
    (gate8FastCompound (gate8AddedBound 4) 28 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 28 26
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row29 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 29 b =
    (gate8FastCompound (gate8AddedBound 4) 29 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 29 27
    (by decide +kernel) (by decide +kernel)

end HiddenCircuits.Small
