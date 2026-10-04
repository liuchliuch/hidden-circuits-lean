import HiddenCircuits.Small.Gate8UnitRows
import HiddenCircuits.Small.Gate8R5Rows5

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise5_row60 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 60 b =
    (gate8FastCompound (gate8AddedBound 5) 60 b : ℤ) := by
  exact gate8_unit_row Gate8R5ZRows (gate8AddedBound 5) 60 59
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise5_row61 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 61 b =
    (gate8FastCompound (gate8AddedBound 5) 61 b : ℤ) := by
  change ∀ b : Fin 70, ((2:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 4, 1, 1, 2, 4, 8] : Fin 70 → ℕ) b : ℤ) + ((-2:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 2] : Fin 70 → ℕ) b : ℤ) + 0)) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![2, 4, 5, 5] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row62 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 62 b =
    (gate8FastCompound (gate8AddedBound 5) 62 b : ℤ) := by
  exact gate8_unit_row Gate8R5ZRows (gate8AddedBound 5) 62 62
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise5_row63 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 63 b =
    (gate8FastCompound (gate8AddedBound 5) 63 b : ℤ) := by
  exact gate8_unit_row Gate8R5ZRows (gate8AddedBound 5) 63 62
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise5_row64 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 64 b =
    (gate8FastCompound (gate8AddedBound 5) 64 b : ℤ) := by
  change ∀ b : Fin 70, ((2:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![2, 5, 5, 7] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row65 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 65 b =
    (gate8FastCompound (gate8AddedBound 5) 65 b : ℤ) := by
  change ∀ b : Fin 70, ((2:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 4, 8] : Fin 70 → ℕ) b : ℤ) + ((-2:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2] : Fin 70 → ℕ) b : ℤ) + 0)) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![3, 4, 5, 5] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row66 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 66 b =
    (gate8FastCompound (gate8AddedBound 5) 66 b : ℤ) := by
  exact gate8_unit_row Gate8R5ZRows (gate8AddedBound 5) 66 66
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise5_row67 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 67 b =
    (gate8FastCompound (gate8AddedBound 5) 67 b : ℤ) := by
  exact gate8_unit_row Gate8R5ZRows (gate8AddedBound 5) 67 66
    (by decide +kernel) (by decide +kernel)

theorem gate8_rise5_row68 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 68 b =
    (gate8FastCompound (gate8AddedBound 5) 68 b : ℤ) := by
  change ∀ b : Fin 70, ((2:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![3, 5, 5, 7] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row69 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 69 b =
    (gate8FastCompound (gate8AddedBound 5) 69 b : ℤ) := by
  change ∀ b : Fin 70, ((2:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![4, 5, 5, 7] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel


end HiddenCircuits.Small
