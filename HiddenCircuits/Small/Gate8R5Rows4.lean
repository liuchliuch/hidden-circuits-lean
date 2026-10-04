import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8R5Rows3

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise5_row40 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 40 b =
    (gate8FastCompound (gate8AddedBound 5) 40 b : ℤ) := by
  exact gate8_unit_row Gate8R5ZRows (gate8AddedBound 5) 40 39
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise5_row41 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 41 b =
    (gate8FastCompound (gate8AddedBound 5) 41 b : ℤ) := by
  exact gate8_unit_row Gate8R5ZRows (gate8AddedBound 5) 41 41
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise5_row42 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 42 b =
    (gate8FastCompound (gate8AddedBound 5) 42 b : ℤ) := by
  change ∀ b : Fin 70, ((2:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 1, 1, 2, 1, 1, 2, 4, 0, 0, 0, 2, 2, 4, 2, 2, 4, 8, 2, 2, 4, 8, 8] : Fin 70 → ℕ) b : ℤ) + ((-2:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 2, 0, 0, 2, 2, 0, 0, 2, 2, 2] : Fin 70 → ℕ) b : ℤ) + 0)) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![1, 2, 5, 5] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row43 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 43 b =
    (gate8FastCompound (gate8AddedBound 5) 43 b : ℤ) := by
  exact gate8_unit_row Gate8R5ZRows (gate8AddedBound 5) 43 43
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise5_row44 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 44 b =
    (gate8FastCompound (gate8AddedBound 5) 44 b : ℤ) := by
  exact gate8_unit_row Gate8R5ZRows (gate8AddedBound 5) 44 43
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise5_row45 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 45 b =
    (gate8FastCompound (gate8AddedBound 5) 45 b : ℤ) := by
  exact gate8_unit_row Gate8R5ZRows (gate8AddedBound 5) 45 45
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise5_row46 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 46 b =
    (gate8FastCompound (gate8AddedBound 5) 46 b : ℤ) := by
  exact gate8_unit_row Gate8R5ZRows (gate8AddedBound 5) 46 45
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise5_row47 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 47 b =
    (gate8FastCompound (gate8AddedBound 5) 47 b : ℤ) := by
  exact gate8_unit_row Gate8R5ZRows (gate8AddedBound 5) 47 47
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise5_row48 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 48 b =
    (gate8FastCompound (gate8AddedBound 5) 48 b : ℤ) := by
  change ∀ b : Fin 70, ((2:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 1, 1, 2, 4, 0, 0, 0, 1, 1, 2, 1, 1, 2, 4, 2, 2, 4, 8, 8] : Fin 70 → ℕ) b : ℤ) + ((-2:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 2, 2, 2] : Fin 70 → ℕ) b : ℤ) + 0)) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![1, 3, 5, 5] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row49 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 49 b =
    (gate8FastCompound (gate8AddedBound 5) 49 b : ℤ) := by
  exact gate8_unit_row Gate8R5ZRows (gate8AddedBound 5) 49 49
    (by decide +kernel) (by decide +kernel)

end HiddenCircuits.Small
