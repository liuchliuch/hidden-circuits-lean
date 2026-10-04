import HiddenCircuits.Small.Gate8R5Rows0

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise5_row10 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 10 b =
    (gate8FastCompound (gate8AddedBound 5) 10 b : ℤ) := by
  change ∀ b : Fin 70, ((1:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 2, 4, 4, 4, 6, 0, 0, 0, 0, 2, 2, 2, 4, 4, 4, 2, 2, 2, 4, 4, 4, 8, 8, 8, 12, 2, 2, 2, 4, 4, 4, 8, 8, 8, 12, 8, 8, 8, 12, 18] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![0, 1, 4, 5] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row11 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 11 b =
    (gate8FastCompound (gate8AddedBound 5) 11 b : ℤ) := by
  change ∀ b : Fin 70, ((1:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 0, 0, 2, 0, 2, 2, 0, 4, 4, 4, 0, 0, 2, 0, 2, 2, 0, 4, 4, 4, 0, 4, 4, 4, 6] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![0, 1, 4, 7] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row12 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 12 b =
    (gate8FastCompound (gate8AddedBound 5) 12 b : ℤ) := by
  change ∀ b : Fin 70, ((2:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 1, 1, 2, 1, 1, 2, 4, 0, 0, 0, 0, 0, 0, 0, 2, 2, 4, 0, 0, 0, 2, 2, 4, 2, 2, 4, 8, 0, 0, 0, 2, 2, 4, 2, 2, 4, 8, 2, 2, 4, 8, 8] : Fin 70 → ℕ) b : ℤ) + ((-2:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 2, 0, 0, 2, 2, 2] : Fin 70 → ℕ) b : ℤ) + 0)) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![0, 1, 5, 5] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row13 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 13 b =
    (gate8FastCompound (gate8AddedBound 5) 13 b : ℤ) := by
  change ∀ b : Fin 70, ((1:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 2, 2, 0, 2, 2, 4, 0, 0, 0, 0, 2, 2, 0, 2, 2, 4, 0, 2, 2, 4, 4] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![0, 1, 5, 7] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row14 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 14 b =
    (gate8FastCompound (gate8AddedBound 5) 14 b : ℤ) := by
  change ∀ b : Fin 70, ((1:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 2, 2, 0, 2, 2, 4, 0, 0, 0, 0, 2, 2, 0, 2, 2, 4, 0, 2, 2, 4, 4] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![0, 1, 5, 7] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row15 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 15 b =
    (gate8FastCompound (gate8AddedBound 5) 15 b : ℤ) := by
  change ∀ b : Fin 70, ((1:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 6, 6, 6, 6, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 6, 6, 6, 6, 8, 8, 8, 8, 8, 8, 12, 12, 12, 12, 18, 18, 18, 18, 24] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![0, 2, 3, 4] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row16 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 16 b =
    (gate8FastCompound (gate8AddedBound 5) 16 b : ℤ) := by
  change ∀ b : Fin 70, ((1:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 6, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 8, 8, 8, 8, 8, 8, 12, 12, 12, 12, 18, 18] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![0, 2, 3, 5] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row17 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 17 b =
    (gate8FastCompound (gate8AddedBound 5) 17 b : ℤ) := by
  change ∀ b : Fin 70, ((1:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 6, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 8, 8, 8, 8, 8, 8, 12, 12, 12, 12, 18, 18] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![0, 2, 3, 5] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row18 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 18 b =
    (gate8FastCompound (gate8AddedBound 5) 18 b : ℤ) := by
  change ∀ b : Fin 70, ((1:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 2, 0, 2, 2, 0, 2, 2, 2, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 2, 0, 2, 2, 0, 2, 2, 2, 0, 0, 4, 0, 4, 4, 0, 4, 4, 4, 0, 6, 6, 6, 6] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![0, 2, 3, 7] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row19 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 19 b =
    (gate8FastCompound (gate8AddedBound 5) 19 b : ℤ) := by
  change ∀ b : Fin 70, ((1:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 2, 4, 4, 4, 6, 0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 2, 4, 4, 4, 6, 2, 2, 2, 4, 4, 4, 8, 8, 8, 12, 8, 8, 8, 12, 18] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![0, 2, 4, 5] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel


end HiddenCircuits.Small
