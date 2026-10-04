import HiddenCircuits.Small.Gate8R5Rows1

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise5_row20 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 20 b =
    (gate8FastCompound (gate8AddedBound 5) 20 b : ℤ) := by
  change ∀ b : Fin 70, ((1:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 2, 4, 4, 4, 6, 0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 2, 4, 4, 4, 6, 2, 2, 2, 4, 4, 4, 8, 8, 8, 12, 8, 8, 8, 12, 18] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![0, 2, 4, 5] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row21 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 21 b =
    (gate8FastCompound (gate8AddedBound 5) 21 b : ℤ) := by
  change ∀ b : Fin 70, ((1:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 2, 2, 2, 0, 0, 2, 0, 2, 2, 0, 4, 4, 4, 0, 4, 4, 4, 6] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![0, 2, 4, 7] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row22 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 22 b =
    (gate8FastCompound (gate8AddedBound 5) 22 b : ℤ) := by
  change ∀ b : Fin 70, ((2:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 1, 1, 2, 1, 1, 2, 4, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 1, 1, 2, 1, 1, 2, 4, 0, 0, 0, 2, 2, 4, 2, 2, 4, 8, 2, 2, 4, 8, 8] : Fin 70 → ℕ) b : ℤ) + ((-2:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 2, 0, 0, 2, 2, 0, 0, 2, 2, 2] : Fin 70 → ℕ) b : ℤ) + 0)) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![0, 2, 5, 5] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row23 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 23 b =
    (gate8FastCompound (gate8AddedBound 5) 23 b : ℤ) := by
  change ∀ b : Fin 70, ((1:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 2, 0, 0, 0, 0, 2, 2, 0, 2, 2, 4, 0, 2, 2, 4, 4] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![0, 2, 5, 7] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row24 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 24 b =
    (gate8FastCompound (gate8AddedBound 5) 24 b : ℤ) := by
  change ∀ b : Fin 70, ((1:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 2, 0, 0, 0, 0, 2, 2, 0, 2, 2, 4, 0, 2, 2, 4, 4] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![0, 2, 5, 7] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row25 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 25 b =
    (gate8FastCompound (gate8AddedBound 5) 25 b : ℤ) := by
  change ∀ b : Fin 70, ((1:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 4, 4, 4, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 4, 4, 4, 6, 1, 1, 1, 2, 2, 2, 4, 4, 4, 6, 8, 8, 8, 12, 18] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![0, 3, 4, 5] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row26 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 26 b =
    (gate8FastCompound (gate8AddedBound 5) 26 b : ℤ) := by
  change ∀ b : Fin 70, ((1:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 4, 4, 4, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 4, 4, 4, 6, 1, 1, 1, 2, 2, 2, 4, 4, 4, 6, 8, 8, 8, 12, 18] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![0, 3, 4, 5] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row27 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 27 b =
    (gate8FastCompound (gate8AddedBound 5) 27 b : ℤ) := by
  change ∀ b : Fin 70, ((1:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 2, 2, 2, 0, 0, 1, 0, 1, 1, 0, 2, 2, 2, 0, 4, 4, 4, 6] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![0, 3, 4, 7] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row28 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 28 b =
    (gate8FastCompound (gate8AddedBound 5) 28 b : ℤ) := by
  change ∀ b : Fin 70, ((2:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 1, 1, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 1, 1, 2, 4, 0, 0, 0, 1, 1, 2, 1, 1, 2, 4, 2, 2, 4, 8, 8] : Fin 70 → ℕ) b : ℤ) + ((-2:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 2, 2, 2] : Fin 70 → ℕ) b : ℤ) + 0)) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![0, 3, 5, 5] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row29 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 29 b =
    (gate8FastCompound (gate8AddedBound 5) 29 b : ℤ) := by
  change ∀ b : Fin 70, ((1:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 1, 2, 0, 2, 2, 4, 4] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![0, 3, 5, 7] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel


end HiddenCircuits.Small
