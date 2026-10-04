import HiddenCircuits.Small.Gate8R5Rows6

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise5 : compress gate8Enum (rise 8 4 5) = Gate8R5 := by
  unfold rise
  apply normalized_of_mul_upper gate8Enum
  rw [gate8_compound_upper, Gate8R5, sparseMatrix_mul, ← gate8_added_cast 5,
    gate8_compound_cast, gate8AddedNat_ferrers, gate8_fast_compound]
  unfold Gate8R5Rows Gate8F
  apply sparseProduct_intCast_eq
  ext a b
  fin_cases a
  · exact gate8_rise5_row0 b
  · exact gate8_rise5_row1 b
  · exact gate8_rise5_row2 b
  · exact gate8_rise5_row3 b
  · exact gate8_rise5_row4 b
  · exact gate8_rise5_row5 b
  · exact gate8_rise5_row6 b
  · exact gate8_rise5_row7 b
  · exact gate8_rise5_row8 b
  · exact gate8_rise5_row9 b
  · exact gate8_rise5_row10 b
  · exact gate8_rise5_row11 b
  · exact gate8_rise5_row12 b
  · exact gate8_rise5_row13 b
  · exact gate8_rise5_row14 b
  · exact gate8_rise5_row15 b
  · exact gate8_rise5_row16 b
  · exact gate8_rise5_row17 b
  · exact gate8_rise5_row18 b
  · exact gate8_rise5_row19 b
  · exact gate8_rise5_row20 b
  · exact gate8_rise5_row21 b
  · exact gate8_rise5_row22 b
  · exact gate8_rise5_row23 b
  · exact gate8_rise5_row24 b
  · exact gate8_rise5_row25 b
  · exact gate8_rise5_row26 b
  · exact gate8_rise5_row27 b
  · exact gate8_rise5_row28 b
  · exact gate8_rise5_row29 b
  · exact gate8_rise5_row30 b
  · exact gate8_rise5_row31 b
  · exact gate8_rise5_row32 b
  · exact gate8_rise5_row33 b
  · exact gate8_rise5_row34 b
  · exact gate8_rise5_row35 b
  · exact gate8_rise5_row36 b
  · exact gate8_rise5_row37 b
  · exact gate8_rise5_row38 b
  · exact gate8_rise5_row39 b
  · exact gate8_rise5_row40 b
  · exact gate8_rise5_row41 b
  · exact gate8_rise5_row42 b
  · exact gate8_rise5_row43 b
  · exact gate8_rise5_row44 b
  · exact gate8_rise5_row45 b
  · exact gate8_rise5_row46 b
  · exact gate8_rise5_row47 b
  · exact gate8_rise5_row48 b
  · exact gate8_rise5_row49 b
  · exact gate8_rise5_row50 b
  · exact gate8_rise5_row51 b
  · exact gate8_rise5_row52 b
  · exact gate8_rise5_row53 b
  · exact gate8_rise5_row54 b
  · exact gate8_rise5_row55 b
  · exact gate8_rise5_row56 b
  · exact gate8_rise5_row57 b
  · exact gate8_rise5_row58 b
  · exact gate8_rise5_row59 b
  · exact gate8_rise5_row60 b
  · exact gate8_rise5_row61 b
  · exact gate8_rise5_row62 b
  · exact gate8_rise5_row63 b
  · exact gate8_rise5_row64 b
  · exact gate8_rise5_row65 b
  · exact gate8_rise5_row66 b
  · exact gate8_rise5_row67 b
  · exact gate8_rise5_row68 b
  · exact gate8_rise5_row69 b

end HiddenCircuits.Small
