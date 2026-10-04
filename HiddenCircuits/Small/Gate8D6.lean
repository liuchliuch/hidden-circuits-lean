import HiddenCircuits.Small.Gate8D6Rows6

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem gate8_drop6 : compress gate8Enum (drop 8 4 6) = Gate8D6 := by
  unfold drop
  apply normalized_of_mul_upper gate8Enum
  rw [gate8_compound_upper, Gate8D6, sparseMatrix_mul, ← gate8_deleted_cast 6,
    gate8_compound_cast, gate8DeletedNat_ferrers, gate8_fast_compound]
  unfold Gate8D6Rows Gate8F
  apply sparseProduct_intCast_eq
  ext a b
  fin_cases a
  · exact gate8_drop6_row0 b
  · exact gate8_drop6_row1 b
  · exact gate8_drop6_row2 b
  · exact gate8_drop6_row3 b
  · exact gate8_drop6_row4 b
  · exact gate8_drop6_row5 b
  · exact gate8_drop6_row6 b
  · exact gate8_drop6_row7 b
  · exact gate8_drop6_row8 b
  · exact gate8_drop6_row9 b
  · exact gate8_drop6_row10 b
  · exact gate8_drop6_row11 b
  · exact gate8_drop6_row12 b
  · exact gate8_drop6_row13 b
  · exact gate8_drop6_row14 b
  · exact gate8_drop6_row15 b
  · exact gate8_drop6_row16 b
  · exact gate8_drop6_row17 b
  · exact gate8_drop6_row18 b
  · exact gate8_drop6_row19 b
  · exact gate8_drop6_row20 b
  · exact gate8_drop6_row21 b
  · exact gate8_drop6_row22 b
  · exact gate8_drop6_row23 b
  · exact gate8_drop6_row24 b
  · exact gate8_drop6_row25 b
  · exact gate8_drop6_row26 b
  · exact gate8_drop6_row27 b
  · exact gate8_drop6_row28 b
  · exact gate8_drop6_row29 b
  · exact gate8_drop6_row30 b
  · exact gate8_drop6_row31 b
  · exact gate8_drop6_row32 b
  · exact gate8_drop6_row33 b
  · exact gate8_drop6_row34 b
  · exact gate8_drop6_row35 b
  · exact gate8_drop6_row36 b
  · exact gate8_drop6_row37 b
  · exact gate8_drop6_row38 b
  · exact gate8_drop6_row39 b
  · exact gate8_drop6_row40 b
  · exact gate8_drop6_row41 b
  · exact gate8_drop6_row42 b
  · exact gate8_drop6_row43 b
  · exact gate8_drop6_row44 b
  · exact gate8_drop6_row45 b
  · exact gate8_drop6_row46 b
  · exact gate8_drop6_row47 b
  · exact gate8_drop6_row48 b
  · exact gate8_drop6_row49 b
  · exact gate8_drop6_row50 b
  · exact gate8_drop6_row51 b
  · exact gate8_drop6_row52 b
  · exact gate8_drop6_row53 b
  · exact gate8_drop6_row54 b
  · exact gate8_drop6_row55 b
  · exact gate8_drop6_row56 b
  · exact gate8_drop6_row57 b
  · exact gate8_drop6_row58 b
  · exact gate8_drop6_row59 b
  · exact gate8_drop6_row60 b
  · exact gate8_drop6_row61 b
  · exact gate8_drop6_row62 b
  · exact gate8_drop6_row63 b
  · exact gate8_drop6_row64 b
  · exact gate8_drop6_row65 b
  · exact gate8_drop6_row66 b
  · exact gate8_drop6_row67 b
  · exact gate8_drop6_row68 b
  · exact gate8_drop6_row69 b

end HiddenCircuits.Small
