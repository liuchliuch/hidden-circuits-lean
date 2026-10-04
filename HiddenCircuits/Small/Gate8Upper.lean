import HiddenCircuits.Small.Gate8UpperRows6

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_upper_nat : gate8FastCompound id = Gate8FNat := by
  ext a b
  fin_cases a
  · exact gate8_upper_nat_row0 b
  · exact gate8_upper_nat_row1 b
  · exact gate8_upper_nat_row2 b
  · exact gate8_upper_nat_row3 b
  · exact gate8_upper_nat_row4 b
  · exact gate8_upper_nat_row5 b
  · exact gate8_upper_nat_row6 b
  · exact gate8_upper_nat_row7 b
  · exact gate8_upper_nat_row8 b
  · exact gate8_upper_nat_row9 b
  · exact gate8_upper_nat_row10 b
  · exact gate8_upper_nat_row11 b
  · exact gate8_upper_nat_row12 b
  · exact gate8_upper_nat_row13 b
  · exact gate8_upper_nat_row14 b
  · exact gate8_upper_nat_row15 b
  · exact gate8_upper_nat_row16 b
  · exact gate8_upper_nat_row17 b
  · exact gate8_upper_nat_row18 b
  · exact gate8_upper_nat_row19 b
  · exact gate8_upper_nat_row20 b
  · exact gate8_upper_nat_row21 b
  · exact gate8_upper_nat_row22 b
  · exact gate8_upper_nat_row23 b
  · exact gate8_upper_nat_row24 b
  · exact gate8_upper_nat_row25 b
  · exact gate8_upper_nat_row26 b
  · exact gate8_upper_nat_row27 b
  · exact gate8_upper_nat_row28 b
  · exact gate8_upper_nat_row29 b
  · exact gate8_upper_nat_row30 b
  · exact gate8_upper_nat_row31 b
  · exact gate8_upper_nat_row32 b
  · exact gate8_upper_nat_row33 b
  · exact gate8_upper_nat_row34 b
  · exact gate8_upper_nat_row35 b
  · exact gate8_upper_nat_row36 b
  · exact gate8_upper_nat_row37 b
  · exact gate8_upper_nat_row38 b
  · exact gate8_upper_nat_row39 b
  · exact gate8_upper_nat_row40 b
  · exact gate8_upper_nat_row41 b
  · exact gate8_upper_nat_row42 b
  · exact gate8_upper_nat_row43 b
  · exact gate8_upper_nat_row44 b
  · exact gate8_upper_nat_row45 b
  · exact gate8_upper_nat_row46 b
  · exact gate8_upper_nat_row47 b
  · exact gate8_upper_nat_row48 b
  · exact gate8_upper_nat_row49 b
  · exact gate8_upper_nat_row50 b
  · exact gate8_upper_nat_row51 b
  · exact gate8_upper_nat_row52 b
  · exact gate8_upper_nat_row53 b
  · exact gate8_upper_nat_row54 b
  · exact gate8_upper_nat_row55 b
  · exact gate8_upper_nat_row56 b
  · exact gate8_upper_nat_row57 b
  · exact gate8_upper_nat_row58 b
  · exact gate8_upper_nat_row59 b
  · exact gate8_upper_nat_row60 b
  · exact gate8_upper_nat_row61 b
  · exact gate8_upper_nat_row62 b
  · exact gate8_upper_nat_row63 b
  · exact gate8_upper_nat_row64 b
  · exact gate8_upper_nat_row65 b
  · exact gate8_upper_nat_row66 b
  · exact gate8_upper_nat_row67 b
  · exact gate8_upper_nat_row68 b
  · exact gate8_upper_nat_row69 b

theorem gate8_compound_upper : compress gate8Enum (compound (upper 8)) = Gate8F := by
  rw [← gate8_upper_cast, gate8_compound_cast]
  change (fun a b => (gate8NatCompound (gate8FerrersCut id) a b : ℚ)) = Gate8F
  rw [gate8_fast_compound, gate8_upper_nat]
  rfl

end HiddenCircuits.Small
