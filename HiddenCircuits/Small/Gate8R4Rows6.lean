import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8R4Rows5

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise4_row60 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 60 b =
    (gate8FastCompound (gate8AddedBound 4) 60 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 60 60
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row61 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 61 b =
    (gate8FastCompound (gate8AddedBound 4) 61 b : ℤ) := by
  decide +kernel

theorem gate8_rise4_row62 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 62 b =
    (gate8FastCompound (gate8AddedBound 4) 62 b : ℤ) := by
  decide +kernel

theorem gate8_rise4_row63 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 63 b =
    (gate8FastCompound (gate8AddedBound 4) 63 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 63 63
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row64 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 64 b =
    (gate8FastCompound (gate8AddedBound 4) 64 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 64 63
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row65 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 65 b =
    (gate8FastCompound (gate8AddedBound 4) 65 b : ℤ) := by
  decide +kernel

theorem gate8_rise4_row66 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 66 b =
    (gate8FastCompound (gate8AddedBound 4) 66 b : ℤ) := by
  decide +kernel

theorem gate8_rise4_row67 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 67 b =
    (gate8FastCompound (gate8AddedBound 4) 67 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 67 67
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row68 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 68 b =
    (gate8FastCompound (gate8AddedBound 4) 68 b : ℤ) := by
  exact gate8_unit_row Gate8R4ZRows (gate8AddedBound 4) 68 67
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise4_row69 : ∀ b, sparseIntProduct Gate8R4ZRows Gate8FNat 69 b =
    (gate8FastCompound (gate8AddedBound 4) 69 b : ℤ) := by
  decide +kernel


end HiddenCircuits.Small
