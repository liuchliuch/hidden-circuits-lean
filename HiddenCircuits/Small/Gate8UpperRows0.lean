import HiddenCircuits.Small.Gate8Data

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_upper_nat_row0 : ∀ b, gate8FastCompound id 0 b = Gate8FNat 0 b := by
  decide +kernel

theorem gate8_upper_nat_row1 : ∀ b, gate8FastCompound id 1 b = Gate8FNat 1 b := by
  decide +kernel

theorem gate8_upper_nat_row2 : ∀ b, gate8FastCompound id 2 b = Gate8FNat 2 b := by
  decide +kernel

theorem gate8_upper_nat_row3 : ∀ b, gate8FastCompound id 3 b = Gate8FNat 3 b := by
  decide +kernel

theorem gate8_upper_nat_row4 : ∀ b, gate8FastCompound id 4 b = Gate8FNat 4 b := by
  decide +kernel

theorem gate8_upper_nat_row5 : ∀ b, gate8FastCompound id 5 b = Gate8FNat 5 b := by
  decide +kernel

theorem gate8_upper_nat_row6 : ∀ b, gate8FastCompound id 6 b = Gate8FNat 6 b := by
  decide +kernel

theorem gate8_upper_nat_row7 : ∀ b, gate8FastCompound id 7 b = Gate8FNat 7 b := by
  decide +kernel

theorem gate8_upper_nat_row8 : ∀ b, gate8FastCompound id 8 b = Gate8FNat 8 b := by
  decide +kernel

theorem gate8_upper_nat_row9 : ∀ b, gate8FastCompound id 9 b = Gate8FNat 9 b := by
  decide +kernel


end HiddenCircuits.Small
