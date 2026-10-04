import HiddenCircuits.Small.Gate8R3Rows6

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise3 : compress gate8Enum (rise 8 4 3) = Gate8R3 := by
  unfold rise
  apply normalized_of_mul_upper gate8Enum
  rw [gate8_compound_upper, Gate8R3, sparseMatrix_mul, ← gate8_added_cast 3,
    gate8_compound_cast, gate8AddedNat_ferrers, gate8_fast_compound]
  unfold Gate8R3Rows Gate8F
  apply sparseProduct_intCast_eq
  ext a b
  fin_cases a
  · exact gate8_rise3_row0 b
  · exact gate8_rise3_row1 b
  · exact gate8_rise3_row2 b
  · exact gate8_rise3_row3 b
  · exact gate8_rise3_row4 b
  · exact gate8_rise3_row5 b
  · exact gate8_rise3_row6 b
  · exact gate8_rise3_row7 b
  · exact gate8_rise3_row8 b
  · exact gate8_rise3_row9 b
  · exact gate8_rise3_row10 b
  · exact gate8_rise3_row11 b
  · exact gate8_rise3_row12 b
  · exact gate8_rise3_row13 b
  · exact gate8_rise3_row14 b
  · exact gate8_rise3_row15 b
  · exact gate8_rise3_row16 b
  · exact gate8_rise3_row17 b
  · exact gate8_rise3_row18 b
  · exact gate8_rise3_row19 b
  · exact gate8_rise3_row20 b
  · exact gate8_rise3_row21 b
  · exact gate8_rise3_row22 b
  · exact gate8_rise3_row23 b
  · exact gate8_rise3_row24 b
  · exact gate8_rise3_row25 b
  · exact gate8_rise3_row26 b
  · exact gate8_rise3_row27 b
  · exact gate8_rise3_row28 b
  · exact gate8_rise3_row29 b
  · exact gate8_rise3_row30 b
  · exact gate8_rise3_row31 b
  · exact gate8_rise3_row32 b
  · exact gate8_rise3_row33 b
  · exact gate8_rise3_row34 b
  · exact gate8_rise3_row35 b
  · exact gate8_rise3_row36 b
  · exact gate8_rise3_row37 b
  · exact gate8_rise3_row38 b
  · exact gate8_rise3_row39 b
  · exact gate8_rise3_row40 b
  · exact gate8_rise3_row41 b
  · exact gate8_rise3_row42 b
  · exact gate8_rise3_row43 b
  · exact gate8_rise3_row44 b
  · exact gate8_rise3_row45 b
  · exact gate8_rise3_row46 b
  · exact gate8_rise3_row47 b
  · exact gate8_rise3_row48 b
  · exact gate8_rise3_row49 b
  · exact gate8_rise3_row50 b
  · exact gate8_rise3_row51 b
  · exact gate8_rise3_row52 b
  · exact gate8_rise3_row53 b
  · exact gate8_rise3_row54 b
  · exact gate8_rise3_row55 b
  · exact gate8_rise3_row56 b
  · exact gate8_rise3_row57 b
  · exact gate8_rise3_row58 b
  · exact gate8_rise3_row59 b
  · exact gate8_rise3_row60 b
  · exact gate8_rise3_row61 b
  · exact gate8_rise3_row62 b
  · exact gate8_rise3_row63 b
  · exact gate8_rise3_row64 b
  · exact gate8_rise3_row65 b
  · exact gate8_rise3_row66 b
  · exact gate8_rise3_row67 b
  · exact gate8_rise3_row68 b
  · exact gate8_rise3_row69 b

end HiddenCircuits.Small
