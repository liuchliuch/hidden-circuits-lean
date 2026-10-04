import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8R1Rows2

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise1_row30 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 30 b =
    (gate8FastCompound (gate8AddedBound 1) 30 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 30 30
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row31 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 31 b =
    (gate8FastCompound (gate8AddedBound 1) 31 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 31 31
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row32 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 32 b =
    (gate8FastCompound (gate8AddedBound 1) 32 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 32 32
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row33 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 33 b =
    (gate8FastCompound (gate8AddedBound 1) 33 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 33 33
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row34 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 34 b =
    (gate8FastCompound (gate8AddedBound 1) 34 b : ℤ) := by
  exact gate8_unit_row Gate8R1ZRows (gate8AddedBound 1) 34 34
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise1_row35 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 35 b =
    (gate8FastCompound (gate8AddedBound 1) 35 b : ℤ) := by
  decide +kernel

theorem gate8_rise1_row36 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 36 b =
    (gate8FastCompound (gate8AddedBound 1) 36 b : ℤ) := by
  decide +kernel

theorem gate8_rise1_row37 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 37 b =
    (gate8FastCompound (gate8AddedBound 1) 37 b : ℤ) := by
  decide +kernel

theorem gate8_rise1_row38 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 38 b =
    (gate8FastCompound (gate8AddedBound 1) 38 b : ℤ) := by
  decide +kernel

theorem gate8_rise1_row39 : ∀ b, sparseIntProduct Gate8R1ZRows Gate8FNat 39 b =
    (gate8FastCompound (gate8AddedBound 1) 39 b : ℤ) := by
  decide +kernel


end HiddenCircuits.Small
