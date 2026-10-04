import HiddenCircuits.Small.Gate8R1Rows6

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_rise1 : compress gate8Enum (rise 8 4 1) = Gate8R1 := by
  unfold rise
  apply normalized_of_mul_upper gate8Enum
  rw [gate8_compound_upper, Gate8R1, sparseMatrix_mul, ← gate8_added_cast 1,
    gate8_compound_cast, gate8AddedNat_ferrers, gate8_fast_compound]
  unfold Gate8R1Rows Gate8F
  apply sparseProduct_intCast_eq
  ext a b
  fin_cases a
  · exact gate8_rise1_row0 b
  · exact gate8_rise1_row1 b
  · exact gate8_rise1_row2 b
  · exact gate8_rise1_row3 b
  · exact gate8_rise1_row4 b
  · exact gate8_rise1_row5 b
  · exact gate8_rise1_row6 b
  · exact gate8_rise1_row7 b
  · exact gate8_rise1_row8 b
  · exact gate8_rise1_row9 b
  · exact gate8_rise1_row10 b
  · exact gate8_rise1_row11 b
  · exact gate8_rise1_row12 b
  · exact gate8_rise1_row13 b
  · exact gate8_rise1_row14 b
  · exact gate8_rise1_row15 b
  · exact gate8_rise1_row16 b
  · exact gate8_rise1_row17 b
  · exact gate8_rise1_row18 b
  · exact gate8_rise1_row19 b
  · exact gate8_rise1_row20 b
  · exact gate8_rise1_row21 b
  · exact gate8_rise1_row22 b
  · exact gate8_rise1_row23 b
  · exact gate8_rise1_row24 b
  · exact gate8_rise1_row25 b
  · exact gate8_rise1_row26 b
  · exact gate8_rise1_row27 b
  · exact gate8_rise1_row28 b
  · exact gate8_rise1_row29 b
  · exact gate8_rise1_row30 b
  · exact gate8_rise1_row31 b
  · exact gate8_rise1_row32 b
  · exact gate8_rise1_row33 b
  · exact gate8_rise1_row34 b
  · exact gate8_rise1_row35 b
  · exact gate8_rise1_row36 b
  · exact gate8_rise1_row37 b
  · exact gate8_rise1_row38 b
  · exact gate8_rise1_row39 b
  · exact gate8_rise1_row40 b
  · exact gate8_rise1_row41 b
  · exact gate8_rise1_row42 b
  · exact gate8_rise1_row43 b
  · exact gate8_rise1_row44 b
  · exact gate8_rise1_row45 b
  · exact gate8_rise1_row46 b
  · exact gate8_rise1_row47 b
  · exact gate8_rise1_row48 b
  · exact gate8_rise1_row49 b
  · exact gate8_rise1_row50 b
  · exact gate8_rise1_row51 b
  · exact gate8_rise1_row52 b
  · exact gate8_rise1_row53 b
  · exact gate8_rise1_row54 b
  · exact gate8_rise1_row55 b
  · exact gate8_rise1_row56 b
  · exact gate8_rise1_row57 b
  · exact gate8_rise1_row58 b
  · exact gate8_rise1_row59 b
  · exact gate8_rise1_row60 b
  · exact gate8_rise1_row61 b
  · exact gate8_rise1_row62 b
  · exact gate8_rise1_row63 b
  · exact gate8_rise1_row64 b
  · exact gate8_rise1_row65 b
  · exact gate8_rise1_row66 b
  · exact gate8_rise1_row67 b
  · exact gate8_rise1_row68 b
  · exact gate8_rise1_row69 b

end HiddenCircuits.Small
