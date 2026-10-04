import HiddenCircuits.Small.Gate8D2Rows6

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_drop2 : compress gate8Enum (drop 8 4 2) = Gate8D2 := by
  unfold drop
  apply normalized_of_mul_upper gate8Enum
  rw [gate8_compound_upper, Gate8D2, sparseMatrix_mul, ← gate8_deleted_cast 2,
    gate8_compound_cast, gate8DeletedNat_ferrers, gate8_fast_compound]
  unfold Gate8D2Rows Gate8F
  apply sparseProduct_intCast_eq
  ext a b
  fin_cases a
  · exact gate8_drop2_row0 b
  · exact gate8_drop2_row1 b
  · exact gate8_drop2_row2 b
  · exact gate8_drop2_row3 b
  · exact gate8_drop2_row4 b
  · exact gate8_drop2_row5 b
  · exact gate8_drop2_row6 b
  · exact gate8_drop2_row7 b
  · exact gate8_drop2_row8 b
  · exact gate8_drop2_row9 b
  · exact gate8_drop2_row10 b
  · exact gate8_drop2_row11 b
  · exact gate8_drop2_row12 b
  · exact gate8_drop2_row13 b
  · exact gate8_drop2_row14 b
  · exact gate8_drop2_row15 b
  · exact gate8_drop2_row16 b
  · exact gate8_drop2_row17 b
  · exact gate8_drop2_row18 b
  · exact gate8_drop2_row19 b
  · exact gate8_drop2_row20 b
  · exact gate8_drop2_row21 b
  · exact gate8_drop2_row22 b
  · exact gate8_drop2_row23 b
  · exact gate8_drop2_row24 b
  · exact gate8_drop2_row25 b
  · exact gate8_drop2_row26 b
  · exact gate8_drop2_row27 b
  · exact gate8_drop2_row28 b
  · exact gate8_drop2_row29 b
  · exact gate8_drop2_row30 b
  · exact gate8_drop2_row31 b
  · exact gate8_drop2_row32 b
  · exact gate8_drop2_row33 b
  · exact gate8_drop2_row34 b
  · exact gate8_drop2_row35 b
  · exact gate8_drop2_row36 b
  · exact gate8_drop2_row37 b
  · exact gate8_drop2_row38 b
  · exact gate8_drop2_row39 b
  · exact gate8_drop2_row40 b
  · exact gate8_drop2_row41 b
  · exact gate8_drop2_row42 b
  · exact gate8_drop2_row43 b
  · exact gate8_drop2_row44 b
  · exact gate8_drop2_row45 b
  · exact gate8_drop2_row46 b
  · exact gate8_drop2_row47 b
  · exact gate8_drop2_row48 b
  · exact gate8_drop2_row49 b
  · exact gate8_drop2_row50 b
  · exact gate8_drop2_row51 b
  · exact gate8_drop2_row52 b
  · exact gate8_drop2_row53 b
  · exact gate8_drop2_row54 b
  · exact gate8_drop2_row55 b
  · exact gate8_drop2_row56 b
  · exact gate8_drop2_row57 b
  · exact gate8_drop2_row58 b
  · exact gate8_drop2_row59 b
  · exact gate8_drop2_row60 b
  · exact gate8_drop2_row61 b
  · exact gate8_drop2_row62 b
  · exact gate8_drop2_row63 b
  · exact gate8_drop2_row64 b
  · exact gate8_drop2_row65 b
  · exact gate8_drop2_row66 b
  · exact gate8_drop2_row67 b
  · exact gate8_drop2_row68 b
  · exact gate8_drop2_row69 b

end HiddenCircuits.Small
