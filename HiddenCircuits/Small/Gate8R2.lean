import HiddenCircuits.Small.Gate8R2Rows6

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise2 : compress gate8Enum (rise 8 4 2) = Gate8R2 := by
  unfold rise
  apply normalized_of_mul_upper gate8Enum
  rw [gate8_compound_upper, Gate8R2, sparseMatrix_mul, ← gate8_added_cast 2,
    gate8_compound_cast, gate8AddedNat_ferrers, gate8_fast_compound]
  unfold Gate8R2Rows Gate8F
  apply sparseProduct_intCast_eq
  ext a b
  fin_cases a
  · exact gate8_rise2_row0 b
  · exact gate8_rise2_row1 b
  · exact gate8_rise2_row2 b
  · exact gate8_rise2_row3 b
  · exact gate8_rise2_row4 b
  · exact gate8_rise2_row5 b
  · exact gate8_rise2_row6 b
  · exact gate8_rise2_row7 b
  · exact gate8_rise2_row8 b
  · exact gate8_rise2_row9 b
  · exact gate8_rise2_row10 b
  · exact gate8_rise2_row11 b
  · exact gate8_rise2_row12 b
  · exact gate8_rise2_row13 b
  · exact gate8_rise2_row14 b
  · exact gate8_rise2_row15 b
  · exact gate8_rise2_row16 b
  · exact gate8_rise2_row17 b
  · exact gate8_rise2_row18 b
  · exact gate8_rise2_row19 b
  · exact gate8_rise2_row20 b
  · exact gate8_rise2_row21 b
  · exact gate8_rise2_row22 b
  · exact gate8_rise2_row23 b
  · exact gate8_rise2_row24 b
  · exact gate8_rise2_row25 b
  · exact gate8_rise2_row26 b
  · exact gate8_rise2_row27 b
  · exact gate8_rise2_row28 b
  · exact gate8_rise2_row29 b
  · exact gate8_rise2_row30 b
  · exact gate8_rise2_row31 b
  · exact gate8_rise2_row32 b
  · exact gate8_rise2_row33 b
  · exact gate8_rise2_row34 b
  · exact gate8_rise2_row35 b
  · exact gate8_rise2_row36 b
  · exact gate8_rise2_row37 b
  · exact gate8_rise2_row38 b
  · exact gate8_rise2_row39 b
  · exact gate8_rise2_row40 b
  · exact gate8_rise2_row41 b
  · exact gate8_rise2_row42 b
  · exact gate8_rise2_row43 b
  · exact gate8_rise2_row44 b
  · exact gate8_rise2_row45 b
  · exact gate8_rise2_row46 b
  · exact gate8_rise2_row47 b
  · exact gate8_rise2_row48 b
  · exact gate8_rise2_row49 b
  · exact gate8_rise2_row50 b
  · exact gate8_rise2_row51 b
  · exact gate8_rise2_row52 b
  · exact gate8_rise2_row53 b
  · exact gate8_rise2_row54 b
  · exact gate8_rise2_row55 b
  · exact gate8_rise2_row56 b
  · exact gate8_rise2_row57 b
  · exact gate8_rise2_row58 b
  · exact gate8_rise2_row59 b
  · exact gate8_rise2_row60 b
  · exact gate8_rise2_row61 b
  · exact gate8_rise2_row62 b
  · exact gate8_rise2_row63 b
  · exact gate8_rise2_row64 b
  · exact gate8_rise2_row65 b
  · exact gate8_rise2_row66 b
  · exact gate8_rise2_row67 b
  · exact gate8_rise2_row68 b
  · exact gate8_rise2_row69 b

end HiddenCircuits.Small
