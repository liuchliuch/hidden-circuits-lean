import HiddenCircuits.Small.Gate8R0Rows6

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise0 : compress gate8Enum (rise 8 4 0) = Gate8R0 := by
  unfold rise
  apply normalized_of_mul_upper gate8Enum
  rw [gate8_compound_upper, Gate8R0, sparseMatrix_mul, ← gate8_added_cast 0,
    gate8_compound_cast, gate8AddedNat_ferrers, gate8_fast_compound]
  unfold Gate8R0Rows Gate8F
  apply sparseProduct_intCast_eq
  ext a b
  fin_cases a
  · exact gate8_rise0_row0 b
  · exact gate8_rise0_row1 b
  · exact gate8_rise0_row2 b
  · exact gate8_rise0_row3 b
  · exact gate8_rise0_row4 b
  · exact gate8_rise0_row5 b
  · exact gate8_rise0_row6 b
  · exact gate8_rise0_row7 b
  · exact gate8_rise0_row8 b
  · exact gate8_rise0_row9 b
  · exact gate8_rise0_row10 b
  · exact gate8_rise0_row11 b
  · exact gate8_rise0_row12 b
  · exact gate8_rise0_row13 b
  · exact gate8_rise0_row14 b
  · exact gate8_rise0_row15 b
  · exact gate8_rise0_row16 b
  · exact gate8_rise0_row17 b
  · exact gate8_rise0_row18 b
  · exact gate8_rise0_row19 b
  · exact gate8_rise0_row20 b
  · exact gate8_rise0_row21 b
  · exact gate8_rise0_row22 b
  · exact gate8_rise0_row23 b
  · exact gate8_rise0_row24 b
  · exact gate8_rise0_row25 b
  · exact gate8_rise0_row26 b
  · exact gate8_rise0_row27 b
  · exact gate8_rise0_row28 b
  · exact gate8_rise0_row29 b
  · exact gate8_rise0_row30 b
  · exact gate8_rise0_row31 b
  · exact gate8_rise0_row32 b
  · exact gate8_rise0_row33 b
  · exact gate8_rise0_row34 b
  · exact gate8_rise0_row35 b
  · exact gate8_rise0_row36 b
  · exact gate8_rise0_row37 b
  · exact gate8_rise0_row38 b
  · exact gate8_rise0_row39 b
  · exact gate8_rise0_row40 b
  · exact gate8_rise0_row41 b
  · exact gate8_rise0_row42 b
  · exact gate8_rise0_row43 b
  · exact gate8_rise0_row44 b
  · exact gate8_rise0_row45 b
  · exact gate8_rise0_row46 b
  · exact gate8_rise0_row47 b
  · exact gate8_rise0_row48 b
  · exact gate8_rise0_row49 b
  · exact gate8_rise0_row50 b
  · exact gate8_rise0_row51 b
  · exact gate8_rise0_row52 b
  · exact gate8_rise0_row53 b
  · exact gate8_rise0_row54 b
  · exact gate8_rise0_row55 b
  · exact gate8_rise0_row56 b
  · exact gate8_rise0_row57 b
  · exact gate8_rise0_row58 b
  · exact gate8_rise0_row59 b
  · exact gate8_rise0_row60 b
  · exact gate8_rise0_row61 b
  · exact gate8_rise0_row62 b
  · exact gate8_rise0_row63 b
  · exact gate8_rise0_row64 b
  · exact gate8_rise0_row65 b
  · exact gate8_rise0_row66 b
  · exact gate8_rise0_row67 b
  · exact gate8_rise0_row68 b
  · exact gate8_rise0_row69 b

end HiddenCircuits.Small
