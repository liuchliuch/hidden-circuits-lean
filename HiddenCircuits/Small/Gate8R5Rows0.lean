import HiddenCircuits.Small.Gate8R5Data

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise5_row0 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 0 b =
    (gate8FastCompound (gate8AddedBound 5) 0 b : ℤ) := by
  change ∀ b : Fin 70, ((1:ℤ) * ((![1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 24, 24, 24, 24, 24] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![0, 1, 2, 3] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row1 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 1 b =
    (gate8FastCompound (gate8AddedBound 5) 1 b : ℤ) := by
  change ∀ b : Fin 70, ((1:ℤ) * ((![0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 6, 6, 4, 4, 4, 4, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 18, 18, 18, 18, 18, 18, 18, 18, 24] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![0, 1, 2, 4] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row2 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 2 b =
    (gate8FastCompound (gate8AddedBound 5) 2 b : ℤ) := by
  change ∀ b : Fin 70, ((1:ℤ) * ((![0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 0, 2, 2, 2, 2, 2, 2, 4, 4, 4, 2, 2, 2, 4, 4, 4, 4, 4, 4, 6, 0, 4, 4, 4, 4, 4, 4, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 12, 6, 6, 6, 12, 12, 12, 12, 12, 12, 18, 12, 12, 12, 18, 18] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![0, 1, 2, 5] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row3 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 3 b =
    (gate8FastCompound (gate8AddedBound 5) 3 b : ℤ) := by
  change ∀ b : Fin 70, ((1:ℤ) * ((![0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 0, 2, 2, 2, 2, 2, 2, 4, 4, 4, 2, 2, 2, 4, 4, 4, 4, 4, 4, 6, 0, 4, 4, 4, 4, 4, 4, 8, 8, 8, 4, 4, 4, 8, 8, 8, 8, 8, 8, 12, 6, 6, 6, 12, 12, 12, 12, 12, 12, 18, 12, 12, 12, 18, 18] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![0, 1, 2, 5] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row4 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 4 b =
    (gate8FastCompound (gate8AddedBound 5) 4 b : ℤ) := by
  change ∀ b : Fin 70, ((1:ℤ) * ((![0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 2, 0, 0, 2, 0, 2, 2, 0, 0, 2, 0, 2, 2, 0, 2, 2, 2, 0, 0, 0, 4, 0, 0, 4, 0, 4, 4, 0, 0, 4, 0, 4, 4, 0, 4, 4, 4, 0, 0, 6, 0, 6, 6, 0, 6, 6, 6, 0, 6, 6, 6, 6] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![0, 1, 2, 7] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row5 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 5 b =
    (gate8FastCompound (gate8AddedBound 5) 5 b : ℤ) := by
  change ∀ b : Fin 70, ((1:ℤ) * ((![0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 6, 6, 6, 6, 2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 8, 8, 8, 8, 8, 8, 12, 12, 12, 12, 8, 8, 8, 8, 8, 8, 12, 12, 12, 12, 18, 18, 18, 18, 24] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![0, 1, 3, 4] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row6 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 6 b =
    (gate8FastCompound (gate8AddedBound 5) 6 b : ℤ) := by
  change ∀ b : Fin 70, ((1:ℤ) * ((![0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 6, 0, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 8, 8, 8, 8, 8, 8, 12, 4, 4, 4, 8, 8, 8, 8, 8, 8, 12, 12, 12, 12, 18, 18] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![0, 1, 3, 5] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row7 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 7 b =
    (gate8FastCompound (gate8AddedBound 5) 7 b : ℤ) := by
  change ∀ b : Fin 70, ((1:ℤ) * ((![0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 6, 0, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 8, 8, 8, 8, 8, 8, 12, 4, 4, 4, 8, 8, 8, 8, 8, 8, 12, 12, 12, 12, 18, 18] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![0, 1, 3, 5] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row8 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 8 b =
    (gate8FastCompound (gate8AddedBound 5) 8 b : ℤ) := by
  change ∀ b : Fin 70, ((1:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 2, 0, 2, 2, 0, 2, 2, 2, 0, 0, 0, 2, 0, 0, 2, 0, 2, 2, 0, 0, 4, 0, 4, 4, 0, 4, 4, 4, 0, 0, 4, 0, 4, 4, 0, 4, 4, 4, 0, 6, 6, 6, 6] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![0, 1, 3, 7] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel

theorem gate8_rise5_row9 : ∀ b, sparseIntProduct Gate8R5ZRows Gate8FNat 9 b =
    (gate8FastCompound (gate8AddedBound 5) 9 b : ℤ) := by
  change ∀ b : Fin 70, ((1:ℤ) * ((![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 2, 4, 4, 4, 6, 0, 0, 0, 0, 2, 2, 2, 4, 4, 4, 2, 2, 2, 4, 4, 4, 8, 8, 8, 12, 2, 2, 2, 4, 4, 4, 8, 8, 8, 12, 8, 8, 8, 12, 18] : Fin 70 → ℕ) b : ℤ) + 0) =
    (gate8FastPermanent (fun j => gate8Threshold b ((![0, 1, 4, 5] : Fin 4 → Fin 8) j)) : ℤ)
  decide +kernel


end HiddenCircuits.Small
