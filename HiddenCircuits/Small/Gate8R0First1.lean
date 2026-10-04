import HiddenCircuits.Small.Gate8R0First0
namespace HiddenCircuits.Small
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem gate8_rise0_row1 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 1 b =
    (gate8FastCompound (gate8AddedBound 0) 1 b : ℤ) := by
  decide +kernel

end HiddenCircuits.Small
