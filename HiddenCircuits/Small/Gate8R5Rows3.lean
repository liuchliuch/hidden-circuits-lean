import HiddenCircuits.Small.Gate8R5Rows2

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise5_row30 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 30 b =
    (gate8FastCompound (gate8AddedBound 5) 30 b : ℤ) := by
  change ∀ b : Fin 70, ((1:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 1, 2, 0, 2, 2, 4, 4] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![0, 3, 5, 7] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row31 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 31 b =
    (gate8FastCompound (gate8AddedBound 5) 31 b : ℤ) := by
  change ∀ b : Fin 70, ((2:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 4, 0, 0, 0, 0, 0, 0, 1, 1, 2, 4, 1, 1, 2, 4, 8] : Fin 70 → ℕ) b : ℤ) + ((-2:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 2] : Fin 70 → ℕ) b : ℤ) + 0)) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![0, 4, 5, 5] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row32 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 32 b =
    (gate8FastCompound (gate8AddedBound 5) 32 b : ℤ) := by
  change ∀ b : Fin 70, ((1:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 1, 1, 2, 4] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![0, 4, 5, 7] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row33 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 33 b =
    (gate8FastCompound (gate8AddedBound 5) 33 b : ℤ) := by
  change ∀ b : Fin 70, ((1:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 1, 1, 2, 4] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![0, 4, 5, 7] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row34 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 34 b =
    (gate8FastCompound (gate8AddedBound 5) 34 b : ℤ) := by
  change ∀ b : Fin 70, ((2:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![0, 5, 5, 7] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row35 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 35 b =
    (gate8FastCompound (gate8AddedBound 5) 35 b : ℤ) := by
  change ∀ b : Fin 70, ((1:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 6, 6, 6, 6, 8, 8, 8, 8, 8, 8, 12, 12, 12, 12, 18, 18, 18, 18, 24] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![1, 2, 3, 4] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row36 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 36 b =
    (gate8FastCompound (gate8AddedBound 5) 36 b : ℤ) := by
  change ∀ b : Fin 70, ((1:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 8, 8, 8, 8, 8, 8, 12, 12, 12, 12, 18, 18] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![1, 2, 3, 5] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row37 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 37 b =
    (gate8FastCompound (gate8AddedBound 5) 37 b : ℤ) := by
  change ∀ b : Fin 70, ((1:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 8, 8, 8, 8, 8, 8, 12, 12, 12, 12, 18, 18] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![1, 2, 3, 5] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row38 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 38 b =
    (gate8FastCompound (gate8AddedBound 5) 38 b : ℤ) := by
  change ∀ b : Fin 70, ((1:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 2, 0, 2, 2, 0, 2, 2, 2, 0, 0, 4, 0, 4, 4, 0, 4, 4, 4, 0, 6, 6, 6, 6] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![1, 2, 3, 7] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row39 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 39 b =
    (gate8FastCompound (gate8AddedBound 5) 39 b : ℤ) := by
  change ∀ b : Fin 70, ((1:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 2, 4, 4, 4, 6, 2, 2, 2, 4, 4, 4, 8, 8, 8, 12, 8, 8, 8, 12, 18] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![1, 2, 4, 5] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel


end HiddenCircuits.Small
