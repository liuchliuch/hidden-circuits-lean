import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8R5Rows4

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise5_row50 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 50 b =
    (gate8FastCompound (gate8AddedBound 5) 50 b : ℤ) := by
  exact gate8_unit_row Gate8R5ZRows (gate8AddedBound 5) 50 49
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise5_row51 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 51 b =
    (gate8FastCompound (gate8AddedBound 5) 51 b : ℤ) := by
  change ∀ b : Fin 70, ((2:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 4, 0, 0, 0, 0, 0, 0, 1, 1, 2, 4, 1, 1, 2, 4, 8] : Fin 70 → ℕ) b : ℤ) + ((-2:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 2] : Fin 70 → ℕ) b : ℤ) + 0)) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![1, 4, 5, 5] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row52 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 52 b =
    (gate8FastCompound (gate8AddedBound 5) 52 b : ℤ) := by
  exact gate8_unit_row Gate8R5ZRows (gate8AddedBound 5) 52 52
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise5_row53 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 53 b =
    (gate8FastCompound (gate8AddedBound 5) 53 b : ℤ) := by
  exact gate8_unit_row Gate8R5ZRows (gate8AddedBound 5) 53 52
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise5_row54 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 54 b =
    (gate8FastCompound (gate8AddedBound 5) 54 b : ℤ) := by
  change ∀ b : Fin 70, ((2:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![1, 5, 5, 7] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row55 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 55 b =
    (gate8FastCompound (gate8AddedBound 5) 55 b : ℤ) := by
  exact gate8_unit_row Gate8R5ZRows (gate8AddedBound 5) 55 55
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise5_row56 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 56 b =
    (gate8FastCompound (gate8AddedBound 5) 56 b : ℤ) := by
  exact gate8_unit_row Gate8R5ZRows (gate8AddedBound 5) 56 55
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise5_row57 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 57 b =
    (gate8FastCompound (gate8AddedBound 5) 57 b : ℤ) := by
  exact gate8_unit_row Gate8R5ZRows (gate8AddedBound 5) 57 57
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise5_row58 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 58 b =
    (gate8FastCompound (gate8AddedBound 5) 58 b : ℤ) := by
  change ∀ b : Fin 70, ((2:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 1, 1, 2, 4, 2, 2, 4, 8, 8] : Fin 70 → ℕ) b : ℤ) + ((-2:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 2, 2, 2] : Fin 70 → ℕ) b : ℤ) + 0)) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![2, 3, 5, 5] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row59 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 59 b =
    (gate8FastCompound (gate8AddedBound 5) 59 b : ℤ) := by
  exact gate8_unit_row Gate8R5ZRows (gate8AddedBound 5) 59 59
    (by decide +kernel) (by decide +kernel)

end HiddenCircuits.Small
