import HiddenCircuits.Small.Gate8R0First6
namespace HiddenCircuits.Small
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem gate8_rise0_row7 : ∀ b, sparseIntProduct Gate8R0ZRows Gate8FNat 7 b =
    (gate8FastCompound (gate8AddedBound 0) 7 b : ℤ) := by
  decide +kernel

end HiddenCircuits.Small
