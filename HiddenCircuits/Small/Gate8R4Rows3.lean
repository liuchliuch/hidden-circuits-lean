import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8R4Rows2

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise4_row30 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 30 b =
    (gate8FastCompound (gate8AddedBound 4) 30 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 30 30
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row31 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 31 b =
    (gate8FastCompound (gate8AddedBound 4) 31 b : ℤ) := by
  decide +kernel

theorem gate8_rise4_row32 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 32 b =
    (gate8FastCompound (gate8AddedBound 4) 32 b : ℤ) := by
  decide +kernel

theorem gate8_rise4_row33 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 33 b =
    (gate8FastCompound (gate8AddedBound 4) 33 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 33 33
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row34 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 34 b =
    (gate8FastCompound (gate8AddedBound 4) 34 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 34 33
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row35 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 35 b =
    (gate8FastCompound (gate8AddedBound 4) 35 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 35 35
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row36 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 36 b =
    (gate8FastCompound (gate8AddedBound 4) 36 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 36 35
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row37 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 37 b =
    (gate8FastCompound (gate8AddedBound 4) 37 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 37 37
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row38 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 38 b =
    (gate8FastCompound (gate8AddedBound 4) 38 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 38 38
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row39 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 39 b =
    (gate8FastCompound (gate8AddedBound 4) 39 b : ℤ) := by
  decide +kernel


end HiddenCircuits.Small
