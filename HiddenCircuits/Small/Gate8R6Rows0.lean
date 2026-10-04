import HiddenCircuits.Small.Gate8R6Data

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise6_row0 : ∀ b, sparseIntProduct Gate8R6ZRows Gate8FNat 0 b =
    (gate8FastCompound (gate8AddedBound 6) 0 b : ℤ) := by
  decide +kernel

theorem gate8_rise6_row1 : ∀ b, sparseIntProduct Gate8R6ZRows Gate8FNat 1 b =
    (gate8FastCompound (gate8AddedBound 6) 1 b : ℤ) := by
  decide +kernel

theorem gate8_rise6_row2 : ∀ b, sparseIntProduct Gate8R6ZRows Gate8FNat 2 b =
    (gate8FastCompound (gate8AddedBound 6) 2 b : ℤ) := by
  decide +kernel

theorem gate8_rise6_row3 : ∀ b, sparseIntProduct Gate8R6ZRows Gate8FNat 3 b =
    (gate8FastCompound (gate8AddedBound 6) 3 b : ℤ) := by
  decide +kernel

theorem gate8_rise6_row4 : ∀ b, sparseIntProduct Gate8R6ZRows Gate8FNat 4 b =
    (gate8FastCompound (gate8AddedBound 6) 4 b : ℤ) := by
  decide +kernel

theorem gate8_rise6_row5 : ∀ b, sparseIntProduct Gate8R6ZRows Gate8FNat 5 b =
    (gate8FastCompound (gate8AddedBound 6) 5 b : ℤ) := by
  decide +kernel

theorem gate8_rise6_row6 : ∀ b, sparseIntProduct Gate8R6ZRows Gate8FNat 6 b =
    (gate8FastCompound (gate8AddedBound 6) 6 b : ℤ) := by
  decide +kernel

theorem gate8_rise6_row7 : ∀ b, sparseIntProduct Gate8R6ZRows Gate8FNat 7 b =
    (gate8FastCompound (gate8AddedBound 6) 7 b : ℤ) := by
  decide +kernel

theorem gate8_rise6_row8 : ∀ b, sparseIntProduct Gate8R6ZRows Gate8FNat 8 b =
    (gate8FastCompound (gate8AddedBound 6) 8 b : ℤ) := by
  decide +kernel

theorem gate8_rise6_row9 : ∀ b, sparseIntProduct Gate8R6ZRows Gate8FNat 9 b =
    (gate8FastCompound (gate8AddedBound 6) 9 b : ℤ) := by
  decide +kernel


end HiddenCircuits.Small
