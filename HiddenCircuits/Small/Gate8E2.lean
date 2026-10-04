import HiddenCircuits.Small.Gate8D2

namespace HiddenCircuits.Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def Gate8E2Rows : Fin 70 → List (Fin 70 × ℚ) := ![[(0,1), (9,-2), (10,-4), (11,-8), (12,-6), (13,-12), (14,-18)],
  [(1,1), (5,1), (12,-4), (13,-8), (14,-12)],
  [(2,1), (6,1), (9,2), (14,-8)],
  [(3,1), (7,1), (10,2), (12,4)],
  [(4,1), (8,1), (11,2), (13,4), (14,8)],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [(15,1), (31,2), (32,4), (33,6), (34,12)],
  [(16,1), (33,4), (34,6)],
  [(17,1), (31,-2)],
  [(18,1), (32,-2), (33,-4), (34,-6)],
  [(19,1), (25,1), (34,4)],
  [(20,1), (26,1)],
  [(21,1), (27,1), (34,-4)],
  [(22,1), (28,1), (31,2)],
  [(23,1), (29,1), (32,2)],
  [(24,1), (30,1), (33,2), (34,4)],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [(35,1), (51,2), (52,4), (53,6), (54,12)],
  [(36,1), (53,4), (54,6)],
  [(37,1), (51,-2)],
  [(38,1), (52,-2), (53,-4), (54,-6)],
  [(39,1), (45,1), (54,4)],
  [(40,1), (46,1)],
  [(41,1), (47,1), (54,-4)],
  [(42,1), (48,1), (51,2)],
  [(43,1), (49,1), (52,2)],
  [(44,1), (50,1), (53,2), (54,4)],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [(55,1), (69,-2)],
  [(56,1)],
  [(57,1), (69,2)],
  [(58,1)],
  [(59,1)],
  [(60,1), (69,-2)],
  [(61,1), (65,1)],
  [(62,1), (66,1)],
  [(63,1), (67,1)],
  [(64,1), (68,1), (69,2)],
  [],
  [],
  [],
  [],
  []]
def Gate8E2 : Matrix (Fin 70) (Fin 70) ℚ := sparseMatrix Gate8E2Rows
theorem gate8_dualDrop2_table : ∀ a b, Gate8D2 (gate8Complement b) (gate8Complement a) = Gate8E2 a b := by
  decide +kernel
theorem gate8_dualDrop2 : compress gate8Enum (dualDrop 8 4 2) = Gate8E2 := by
  ext a b
  change drop 8 (8-4) 2 ((gate8States b).complement) ((gate8States a).complement) = _
  rw [gate8States_complement, gate8States_complement]
  change (compress gate8Enum (drop 8 4 2)) (gate8Complement b) (gate8Complement a) = _
  rw [gate8_drop2]
  exact gate8_dualDrop2_table a b

end HiddenCircuits.Small
